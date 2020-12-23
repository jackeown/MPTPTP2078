%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 382 expanded)
%              Number of leaves         :   60 ( 179 expanded)
%              Depth                    :   13
%              Number of atoms          :  649 (1215 expanded)
%              Number of equality atoms :  117 ( 246 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f83,f92,f98,f102,f107,f111,f115,f123,f131,f140,f144,f149,f153,f157,f202,f209,f213,f220,f232,f236,f251,f255,f276,f283,f292,f333,f526,f587,f605,f715,f809,f877,f1038,f1064,f1098,f1103,f1323,f1327,f1331])).

fof(f1331,plain,
    ( spl2_5
    | ~ spl2_28
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f1330])).

fof(f1330,plain,
    ( $false
    | spl2_5
    | ~ spl2_28
    | ~ spl2_92 ),
    inference(subsumption_resolution,[],[f86,f1328])).

fof(f1328,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_28
    | ~ spl2_92 ),
    inference(superposition,[],[f250,f1322])).

fof(f1322,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f1320])).

fof(f1320,plain,
    ( spl2_92
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f250,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl2_28
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f86,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1327,plain,
    ( ~ spl2_11
    | ~ spl2_66
    | ~ spl2_73
    | spl2_91 ),
    inference(avatar_contradiction_clause,[],[f1326])).

fof(f1326,plain,
    ( $false
    | ~ spl2_11
    | ~ spl2_66
    | ~ spl2_73
    | spl2_91 ),
    inference(subsumption_resolution,[],[f961,f1324])).

fof(f1324,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_11
    | spl2_91 ),
    inference(unit_resulting_resolution,[],[f1318,f114])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f1318,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_91 ),
    inference(avatar_component_clause,[],[f1316])).

fof(f1316,plain,
    ( spl2_91
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).

fof(f961,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_66
    | ~ spl2_73 ),
    inference(unit_resulting_resolution,[],[f959,f876])).

fof(f876,plain,
    ( ! [X5] :
        ( r1_tarski(X5,u1_struct_0(sK0))
        | ~ r1_tarski(X5,sK1) )
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f875])).

fof(f875,plain,
    ( spl2_66
  <=> ! [X5] :
        ( r1_tarski(X5,u1_struct_0(sK0))
        | ~ r1_tarski(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f959,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f957])).

fof(f957,plain,
    ( spl2_73
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f1323,plain,
    ( ~ spl2_91
    | spl2_92
    | ~ spl2_3
    | ~ spl2_24
    | ~ spl2_31
    | ~ spl2_58
    | ~ spl2_73 ),
    inference(avatar_split_clause,[],[f1081,f957,f713,f273,f218,f76,f1320,f1316])).

fof(f76,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f218,plain,
    ( spl2_24
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f273,plain,
    ( spl2_31
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f713,plain,
    ( spl2_58
  <=> ! [X1,X2] :
        ( k2_xboole_0(X2,X1) = X2
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f1081,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_24
    | ~ spl2_31
    | ~ spl2_58
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f1080,f974])).

fof(f974,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_58
    | ~ spl2_73 ),
    inference(unit_resulting_resolution,[],[f959,f714])).

fof(f714,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X2,X1) = X2
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f713])).

fof(f1080,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_24
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f277,f78])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f277,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_24
    | ~ spl2_31 ),
    inference(superposition,[],[f275,f219])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f218])).

fof(f275,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f273])).

fof(f1103,plain,
    ( spl2_73
    | ~ spl2_8
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f938,f289,f100,f957])).

fof(f100,plain,
    ( spl2_8
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f289,plain,
    ( spl2_33
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f938,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_8
    | ~ spl2_33 ),
    inference(superposition,[],[f101,f291])).

fof(f291,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f289])).

fof(f101,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1098,plain,
    ( ~ spl2_5
    | ~ spl2_17
    | ~ spl2_29
    | ~ spl2_48
    | ~ spl2_73
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f1079,f1035,f957,f524,f253,f142,f85])).

fof(f142,plain,
    ( spl2_17
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f253,plain,
    ( spl2_29
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f524,plain,
    ( spl2_48
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f1035,plain,
    ( spl2_76
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f1079,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_17
    | ~ spl2_29
    | ~ spl2_48
    | ~ spl2_73
    | ~ spl2_76 ),
    inference(trivial_inequality_removal,[],[f1078])).

fof(f1078,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_17
    | ~ spl2_29
    | ~ spl2_48
    | ~ spl2_73
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f1077,f972])).

fof(f972,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_73 ),
    inference(unit_resulting_resolution,[],[f959,f525])).

fof(f525,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f524])).

fof(f1077,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_17
    | ~ spl2_29
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f1023,f1046])).

fof(f1046,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_17
    | ~ spl2_76 ),
    inference(superposition,[],[f143,f1037])).

fof(f1037,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f143,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f142])).

fof(f1023,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f45,f254])).

fof(f254,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f253])).

fof(f45,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f1064,plain,
    ( ~ spl2_2
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_63
    | spl2_73 ),
    inference(avatar_contradiction_clause,[],[f1063])).

fof(f1063,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_63
    | spl2_73 ),
    inference(subsumption_resolution,[],[f1027,f958])).

fof(f958,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_73 ),
    inference(avatar_component_clause,[],[f957])).

fof(f1027,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_63 ),
    inference(unit_resulting_resolution,[],[f73,f148,f87,f808])).

fof(f808,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_tops_1(X1,X0),X0)
        | ~ v4_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) )
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f807])).

fof(f807,plain,
    ( spl2_63
  <=> ! [X1,X0] :
        ( ~ v4_pre_topc(X0,X1)
        | r1_tarski(k2_tops_1(X1,X0),X0)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f87,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f148,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_18
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1038,plain,
    ( spl2_76
    | ~ spl2_29
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f284,f280,f253,f1035])).

fof(f280,plain,
    ( spl2_32
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f284,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_29
    | ~ spl2_32 ),
    inference(superposition,[],[f282,f254])).

fof(f282,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f280])).

fof(f877,plain,
    ( spl2_66
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f197,f155,f146,f875])).

fof(f155,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f197,plain,
    ( ! [X5] :
        ( r1_tarski(X5,u1_struct_0(sK0))
        | ~ r1_tarski(X5,sK1) )
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(resolution,[],[f156,f148])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f809,plain,
    ( spl2_63
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f222,f211,f113,f807])).

fof(f211,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,X1)
        | r1_tarski(k2_tops_1(X1,X0),X0)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) )
    | ~ spl2_11
    | ~ spl2_23 ),
    inference(resolution,[],[f212,f114])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f211])).

fof(f715,plain,
    ( spl2_58
    | ~ spl2_7
    | ~ spl2_36
    | ~ spl2_51
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f606,f603,f585,f331,f96,f713])).

fof(f96,plain,
    ( spl2_7
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f331,plain,
    ( spl2_36
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f585,plain,
    ( spl2_51
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f603,plain,
    ( spl2_53
  <=> ! [X1,X2] :
        ( k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0)
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f606,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X2,X1) = X2
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_7
    | ~ spl2_36
    | ~ spl2_51
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f604,f596])).

fof(f596,plain,
    ( ! [X10] : k5_xboole_0(X10,k1_xboole_0) = X10
    | ~ spl2_7
    | ~ spl2_36
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f593,f97])).

fof(f97,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f593,plain,
    ( ! [X10] : k4_xboole_0(X10,k1_xboole_0) = k5_xboole_0(X10,k1_xboole_0)
    | ~ spl2_36
    | ~ spl2_51 ),
    inference(superposition,[],[f586,f332])).

fof(f332,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f331])).

fof(f586,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f585])).

fof(f604,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f603])).

fof(f605,plain,
    ( spl2_53
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f173,f138,f129,f603])).

fof(f129,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f138,plain,
    ( spl2_16
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f173,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(superposition,[],[f139,f130])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f139,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f587,plain,
    ( spl2_51
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f184,f151,f105,f585])).

fof(f105,plain,
    ( spl2_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f151,plain,
    ( spl2_19
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f184,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(superposition,[],[f152,f106])).

fof(f106,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f152,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f151])).

fof(f526,plain,
    ( spl2_48
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f160,f121,f105,f524])).

fof(f121,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f160,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(superposition,[],[f122,f106])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f333,plain,
    ( spl2_36
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f158,f121,f81,f331])).

fof(f81,plain,
    ( spl2_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f158,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f82,f122])).

fof(f82,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f292,plain,
    ( ~ spl2_3
    | spl2_33
    | ~ spl2_6
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f204,f200,f89,f289,f76])).

fof(f89,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f200,plain,
    ( spl2_21
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f204,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6
    | ~ spl2_21 ),
    inference(superposition,[],[f201,f91])).

fof(f91,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f201,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f200])).

fof(f283,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f242,f234,f76,f71,f280])).

fof(f234,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f242,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f73,f78,f235])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f234])).

fof(f276,plain,
    ( spl2_31
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f237,f230,f76,f71,f273])).

fof(f230,plain,
    ( spl2_26
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f237,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f73,f78,f231])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f255,plain,
    ( spl2_29
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f203,f200,f76,f253])).

fof(f203,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f78,f201])).

fof(f251,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f214,f207,f76,f71,f66,f248])).

fof(f66,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f207,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f214,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f68,f73,f78,f208])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f207])).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f236,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f49,f234])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f232,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f48,f230])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f220,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f64,f218])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f213,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f50,f211])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f209,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f57,f207])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f202,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f62,f200])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f157,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f63,f155])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f153,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f55,f151])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f149,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f132,f109,f76,f146])).

fof(f109,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f132,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f78,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f144,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f54,f142])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f140,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f53,f138])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f131,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f61,f129])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f123,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f56,f121])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f115,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f59,f113])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f111,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f58,f109])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f107,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f52,f105])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f102,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f51,f100])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f98,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f92,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f44,f89,f85])).

fof(f44,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f79,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f43,f76])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f41,f66])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:47:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (27205)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (27204)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (27206)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (27203)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (27202)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (27215)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (27207)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (27216)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (27214)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (27212)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (27210)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (27211)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (27200)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (27213)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (27201)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (27208)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (27209)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (27217)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (27205)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1332,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f69,f74,f79,f83,f92,f98,f102,f107,f111,f115,f123,f131,f140,f144,f149,f153,f157,f202,f209,f213,f220,f232,f236,f251,f255,f276,f283,f292,f333,f526,f587,f605,f715,f809,f877,f1038,f1064,f1098,f1103,f1323,f1327,f1331])).
% 0.22/0.52  fof(f1331,plain,(
% 0.22/0.52    spl2_5 | ~spl2_28 | ~spl2_92),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1330])).
% 0.22/0.52  fof(f1330,plain,(
% 0.22/0.52    $false | (spl2_5 | ~spl2_28 | ~spl2_92)),
% 0.22/0.52    inference(subsumption_resolution,[],[f86,f1328])).
% 0.22/0.52  fof(f1328,plain,(
% 0.22/0.52    v4_pre_topc(sK1,sK0) | (~spl2_28 | ~spl2_92)),
% 0.22/0.52    inference(superposition,[],[f250,f1322])).
% 0.22/0.52  fof(f1322,plain,(
% 0.22/0.52    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_92),
% 0.22/0.52    inference(avatar_component_clause,[],[f1320])).
% 0.22/0.52  fof(f1320,plain,(
% 0.22/0.52    spl2_92 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 0.22/0.52  fof(f250,plain,(
% 0.22/0.52    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_28),
% 0.22/0.52    inference(avatar_component_clause,[],[f248])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    spl2_28 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ~v4_pre_topc(sK1,sK0) | spl2_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.52  fof(f1327,plain,(
% 0.22/0.52    ~spl2_11 | ~spl2_66 | ~spl2_73 | spl2_91),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1326])).
% 0.22/0.52  fof(f1326,plain,(
% 0.22/0.52    $false | (~spl2_11 | ~spl2_66 | ~spl2_73 | spl2_91)),
% 0.22/0.52    inference(subsumption_resolution,[],[f961,f1324])).
% 0.22/0.52  fof(f1324,plain,(
% 0.22/0.52    ~r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_11 | spl2_91)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f1318,f114])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    spl2_11 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.52  fof(f1318,plain,(
% 0.22/0.52    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_91),
% 0.22/0.52    inference(avatar_component_clause,[],[f1316])).
% 0.22/0.52  fof(f1316,plain,(
% 0.22/0.52    spl2_91 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).
% 0.22/0.52  fof(f961,plain,(
% 0.22/0.52    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_66 | ~spl2_73)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f959,f876])).
% 0.22/0.52  fof(f876,plain,(
% 0.22/0.52    ( ! [X5] : (r1_tarski(X5,u1_struct_0(sK0)) | ~r1_tarski(X5,sK1)) ) | ~spl2_66),
% 0.22/0.52    inference(avatar_component_clause,[],[f875])).
% 0.22/0.52  fof(f875,plain,(
% 0.22/0.52    spl2_66 <=> ! [X5] : (r1_tarski(X5,u1_struct_0(sK0)) | ~r1_tarski(X5,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 0.22/0.52  fof(f959,plain,(
% 0.22/0.52    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_73),
% 0.22/0.52    inference(avatar_component_clause,[],[f957])).
% 0.22/0.52  fof(f957,plain,(
% 0.22/0.52    spl2_73 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 0.22/0.52  fof(f1323,plain,(
% 0.22/0.52    ~spl2_91 | spl2_92 | ~spl2_3 | ~spl2_24 | ~spl2_31 | ~spl2_58 | ~spl2_73),
% 0.22/0.52    inference(avatar_split_clause,[],[f1081,f957,f713,f273,f218,f76,f1320,f1316])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    spl2_24 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.52  fof(f273,plain,(
% 0.22/0.52    spl2_31 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.22/0.52  fof(f713,plain,(
% 0.22/0.52    spl2_58 <=> ! [X1,X2] : (k2_xboole_0(X2,X1) = X2 | ~r1_tarski(X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.22/0.52  fof(f1081,plain,(
% 0.22/0.52    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_24 | ~spl2_31 | ~spl2_58 | ~spl2_73)),
% 0.22/0.52    inference(forward_demodulation,[],[f1080,f974])).
% 0.22/0.52  fof(f974,plain,(
% 0.22/0.52    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_58 | ~spl2_73)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f959,f714])).
% 0.22/0.52  fof(f714,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = X2 | ~r1_tarski(X1,X2)) ) | ~spl2_58),
% 0.22/0.52    inference(avatar_component_clause,[],[f713])).
% 0.22/0.52  fof(f1080,plain,(
% 0.22/0.52    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_24 | ~spl2_31)),
% 0.22/0.52    inference(subsumption_resolution,[],[f277,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f76])).
% 0.22/0.52  fof(f277,plain,(
% 0.22/0.52    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_24 | ~spl2_31)),
% 0.22/0.52    inference(superposition,[],[f275,f219])).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f218])).
% 0.22/0.52  fof(f275,plain,(
% 0.22/0.52    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_31),
% 0.22/0.52    inference(avatar_component_clause,[],[f273])).
% 0.22/0.52  fof(f1103,plain,(
% 0.22/0.52    spl2_73 | ~spl2_8 | ~spl2_33),
% 0.22/0.52    inference(avatar_split_clause,[],[f938,f289,f100,f957])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    spl2_8 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.52  fof(f289,plain,(
% 0.22/0.52    spl2_33 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.22/0.52  fof(f938,plain,(
% 0.22/0.52    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_8 | ~spl2_33)),
% 0.22/0.52    inference(superposition,[],[f101,f291])).
% 0.22/0.52  fof(f291,plain,(
% 0.22/0.52    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_33),
% 0.22/0.52    inference(avatar_component_clause,[],[f289])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f100])).
% 0.22/0.52  fof(f1098,plain,(
% 0.22/0.52    ~spl2_5 | ~spl2_17 | ~spl2_29 | ~spl2_48 | ~spl2_73 | ~spl2_76),
% 0.22/0.52    inference(avatar_split_clause,[],[f1079,f1035,f957,f524,f253,f142,f85])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    spl2_17 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.52  fof(f253,plain,(
% 0.22/0.52    spl2_29 <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.52  fof(f524,plain,(
% 0.22/0.52    spl2_48 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.22/0.52  fof(f1035,plain,(
% 0.22/0.52    spl2_76 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 0.22/0.52  fof(f1079,plain,(
% 0.22/0.52    ~v4_pre_topc(sK1,sK0) | (~spl2_17 | ~spl2_29 | ~spl2_48 | ~spl2_73 | ~spl2_76)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f1078])).
% 0.22/0.52  fof(f1078,plain,(
% 0.22/0.52    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | (~spl2_17 | ~spl2_29 | ~spl2_48 | ~spl2_73 | ~spl2_76)),
% 0.22/0.52    inference(forward_demodulation,[],[f1077,f972])).
% 0.22/0.52  fof(f972,plain,(
% 0.22/0.52    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_48 | ~spl2_73)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f959,f525])).
% 0.22/0.52  fof(f525,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | ~spl2_48),
% 0.22/0.52    inference(avatar_component_clause,[],[f524])).
% 0.22/0.52  fof(f1077,plain,(
% 0.22/0.52    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | (~spl2_17 | ~spl2_29 | ~spl2_76)),
% 0.22/0.52    inference(forward_demodulation,[],[f1023,f1046])).
% 0.22/0.52  fof(f1046,plain,(
% 0.22/0.52    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_17 | ~spl2_76)),
% 0.22/0.52    inference(superposition,[],[f143,f1037])).
% 0.22/0.52  fof(f1037,plain,(
% 0.22/0.52    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_76),
% 0.22/0.52    inference(avatar_component_clause,[],[f1035])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f142])).
% 0.22/0.52  fof(f1023,plain,(
% 0.22/0.52    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_29),
% 0.22/0.52    inference(forward_demodulation,[],[f45,f254])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_29),
% 0.22/0.52    inference(avatar_component_clause,[],[f253])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f18])).
% 0.22/0.52  fof(f18,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.22/0.52  fof(f1064,plain,(
% 0.22/0.52    ~spl2_2 | ~spl2_5 | ~spl2_18 | ~spl2_63 | spl2_73),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1063])).
% 0.22/0.52  fof(f1063,plain,(
% 0.22/0.52    $false | (~spl2_2 | ~spl2_5 | ~spl2_18 | ~spl2_63 | spl2_73)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1027,f958])).
% 0.22/0.52  fof(f958,plain,(
% 0.22/0.52    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_73),
% 0.22/0.52    inference(avatar_component_clause,[],[f957])).
% 0.22/0.52  fof(f1027,plain,(
% 0.22/0.52    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_5 | ~spl2_18 | ~spl2_63)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f73,f148,f87,f808])).
% 0.22/0.52  fof(f808,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X1,X0),X0) | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) ) | ~spl2_63),
% 0.22/0.52    inference(avatar_component_clause,[],[f807])).
% 0.22/0.52  fof(f807,plain,(
% 0.22/0.52    spl2_63 <=> ! [X1,X0] : (~v4_pre_topc(X0,X1) | r1_tarski(k2_tops_1(X1,X0),X0) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f85])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f146])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    spl2_18 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    l1_pre_topc(sK0) | ~spl2_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl2_2 <=> l1_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.52  fof(f1038,plain,(
% 0.22/0.52    spl2_76 | ~spl2_29 | ~spl2_32),
% 0.22/0.52    inference(avatar_split_clause,[],[f284,f280,f253,f1035])).
% 0.22/0.52  fof(f280,plain,(
% 0.22/0.52    spl2_32 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.52  fof(f284,plain,(
% 0.22/0.52    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_29 | ~spl2_32)),
% 0.22/0.52    inference(superposition,[],[f282,f254])).
% 0.22/0.52  fof(f282,plain,(
% 0.22/0.52    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_32),
% 0.22/0.52    inference(avatar_component_clause,[],[f280])).
% 0.22/0.52  fof(f877,plain,(
% 0.22/0.52    spl2_66 | ~spl2_18 | ~spl2_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f197,f155,f146,f875])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    spl2_20 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    ( ! [X5] : (r1_tarski(X5,u1_struct_0(sK0)) | ~r1_tarski(X5,sK1)) ) | (~spl2_18 | ~spl2_20)),
% 0.22/0.52    inference(resolution,[],[f156,f148])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f155])).
% 0.22/0.52  fof(f809,plain,(
% 0.22/0.52    spl2_63 | ~spl2_11 | ~spl2_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f222,f211,f113,f807])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    spl2_23 <=> ! [X1,X0] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v4_pre_topc(X0,X1) | r1_tarski(k2_tops_1(X1,X0),X0) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) ) | (~spl2_11 | ~spl2_23)),
% 0.22/0.52    inference(resolution,[],[f212,f114])).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f211])).
% 0.22/0.52  fof(f715,plain,(
% 0.22/0.52    spl2_58 | ~spl2_7 | ~spl2_36 | ~spl2_51 | ~spl2_53),
% 0.22/0.52    inference(avatar_split_clause,[],[f606,f603,f585,f331,f96,f713])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    spl2_7 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.52  fof(f331,plain,(
% 0.22/0.52    spl2_36 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.22/0.52  fof(f585,plain,(
% 0.22/0.52    spl2_51 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.22/0.52  fof(f603,plain,(
% 0.22/0.52    spl2_53 <=> ! [X1,X2] : (k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.22/0.52  fof(f606,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = X2 | ~r1_tarski(X1,X2)) ) | (~spl2_7 | ~spl2_36 | ~spl2_51 | ~spl2_53)),
% 0.22/0.52    inference(forward_demodulation,[],[f604,f596])).
% 0.22/0.52  fof(f596,plain,(
% 0.22/0.52    ( ! [X10] : (k5_xboole_0(X10,k1_xboole_0) = X10) ) | (~spl2_7 | ~spl2_36 | ~spl2_51)),
% 0.22/0.52    inference(forward_demodulation,[],[f593,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f96])).
% 0.22/0.52  fof(f593,plain,(
% 0.22/0.52    ( ! [X10] : (k4_xboole_0(X10,k1_xboole_0) = k5_xboole_0(X10,k1_xboole_0)) ) | (~spl2_36 | ~spl2_51)),
% 0.22/0.52    inference(superposition,[],[f586,f332])).
% 0.22/0.52  fof(f332,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl2_36),
% 0.22/0.52    inference(avatar_component_clause,[],[f331])).
% 0.22/0.52  fof(f586,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | ~spl2_51),
% 0.22/0.52    inference(avatar_component_clause,[],[f585])).
% 0.22/0.52  fof(f604,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | ~spl2_53),
% 0.22/0.52    inference(avatar_component_clause,[],[f603])).
% 0.22/0.52  fof(f605,plain,(
% 0.22/0.52    spl2_53 | ~spl2_15 | ~spl2_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f173,f138,f129,f603])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    spl2_15 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    spl2_16 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | (~spl2_15 | ~spl2_16)),
% 0.22/0.52    inference(superposition,[],[f139,f130])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl2_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f129])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f138])).
% 0.22/0.52  fof(f587,plain,(
% 0.22/0.52    spl2_51 | ~spl2_9 | ~spl2_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f184,f151,f105,f585])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    spl2_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    spl2_19 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | (~spl2_9 | ~spl2_19)),
% 0.22/0.52    inference(superposition,[],[f152,f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f105])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f151])).
% 0.22/0.52  fof(f526,plain,(
% 0.22/0.52    spl2_48 | ~spl2_9 | ~spl2_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f160,f121,f105,f524])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    spl2_13 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | (~spl2_9 | ~spl2_13)),
% 0.22/0.52    inference(superposition,[],[f122,f106])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f121])).
% 0.22/0.52  fof(f333,plain,(
% 0.22/0.52    spl2_36 | ~spl2_4 | ~spl2_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f158,f121,f81,f331])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl2_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl2_4 | ~spl2_13)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f82,f122])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f292,plain,(
% 0.22/0.52    ~spl2_3 | spl2_33 | ~spl2_6 | ~spl2_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f204,f200,f89,f289,f76])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    spl2_21 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_6 | ~spl2_21)),
% 0.22/0.52    inference(superposition,[],[f201,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f89])).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f200])).
% 0.22/0.52  fof(f283,plain,(
% 0.22/0.52    spl2_32 | ~spl2_2 | ~spl2_3 | ~spl2_27),
% 0.22/0.52    inference(avatar_split_clause,[],[f242,f234,f76,f71,f280])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    spl2_27 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_27)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f73,f78,f235])).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_27),
% 0.22/0.52    inference(avatar_component_clause,[],[f234])).
% 0.22/0.52  fof(f276,plain,(
% 0.22/0.52    spl2_31 | ~spl2_2 | ~spl2_3 | ~spl2_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f237,f230,f76,f71,f273])).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    spl2_26 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_26)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f73,f78,f231])).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f230])).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    spl2_29 | ~spl2_3 | ~spl2_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f203,f200,f76,f253])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl2_3 | ~spl2_21)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f78,f201])).
% 0.22/0.52  fof(f251,plain,(
% 0.22/0.52    spl2_28 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f214,f207,f76,f71,f66,f248])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl2_1 <=> v2_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    spl2_22 <=> ! [X1,X0] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_22)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f68,f73,f78,f208])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f207])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    v2_pre_topc(sK0) | ~spl2_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f66])).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    spl2_27),
% 0.22/0.52    inference(avatar_split_clause,[],[f49,f234])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    spl2_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f230])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    spl2_24),
% 0.22/0.52    inference(avatar_split_clause,[],[f64,f218])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(flattening,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    spl2_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f50,f211])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.22/0.52  fof(f209,plain,(
% 0.22/0.52    spl2_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f57,f207])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    spl2_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f62,f200])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    spl2_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f63,f155])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    spl2_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f55,f151])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    spl2_18 | ~spl2_3 | ~spl2_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f132,f109,f76,f146])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl2_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_3 | ~spl2_10)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f78,f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f109])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    spl2_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f54,f142])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    spl2_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f53,f138])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    spl2_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f61,f129])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    spl2_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f56,f121])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    spl2_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f59,f113])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    spl2_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f58,f109])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl2_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f52,f105])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl2_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f51,f100])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    spl2_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f96])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl2_5 | spl2_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f44,f89,f85])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl2_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f46,f81])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl2_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f43,f76])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl2_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f42,f71])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl2_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f41,f66])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (27205)------------------------------
% 0.22/0.52  % (27205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27205)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (27205)Memory used [KB]: 7036
% 0.22/0.52  % (27205)Time elapsed: 0.094 s
% 0.22/0.52  % (27205)------------------------------
% 0.22/0.52  % (27205)------------------------------
% 0.22/0.52  % (27199)Success in time 0.16 s
%------------------------------------------------------------------------------
