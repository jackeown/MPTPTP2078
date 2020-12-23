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
% DateTime   : Thu Dec  3 13:20:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 374 expanded)
%              Number of leaves         :   35 ( 152 expanded)
%              Depth                    :   14
%              Number of atoms          :  522 (1195 expanded)
%              Number of equality atoms :   47 ( 126 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f668,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f101,f110,f146,f170,f180,f185,f245,f250,f302,f315,f427,f500,f505,f560,f571,f600,f641,f667])).

fof(f667,plain,
    ( spl2_32
    | ~ spl2_33
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | spl2_32
    | ~ spl2_33
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f665,f570])).

fof(f570,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | spl2_32 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl2_32
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f665,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl2_33
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f660,f640])).

fof(f640,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl2_34
  <=> r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f660,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl2_33 ),
    inference(resolution,[],[f599,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f599,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl2_33
  <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f641,plain,
    ( spl2_34
    | ~ spl2_1
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f563,f557,f502,f76,f638])).

fof(f76,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f502,plain,
    ( spl2_30
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f557,plain,
    ( spl2_31
  <=> v1_tops_2(u1_pre_topc(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f563,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl2_1
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(unit_resulting_resolution,[],[f78,f504,f559,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f559,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f557])).

fof(f504,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f502])).

fof(f78,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f600,plain,
    ( spl2_33
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_24
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f555,f497,f424,f167,f81,f597])).

fof(f81,plain,
    ( spl2_2
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f167,plain,
    ( spl2_9
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f424,plain,
    ( spl2_24
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f497,plain,
    ( spl2_29
  <=> v1_tops_2(u1_pre_topc(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f555,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_24
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f554,f169])).

fof(f169,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f554,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ spl2_2
    | ~ spl2_24
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f553,f426])).

fof(f426,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f424])).

fof(f553,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl2_2
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f551,f83])).

fof(f83,plain,
    ( l1_pre_topc(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f551,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ spl2_29 ),
    inference(resolution,[],[f499,f60])).

fof(f499,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f497])).

fof(f571,plain,
    ( ~ spl2_32
    | ~ spl2_11
    | spl2_12
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f475,f424,f182,f177,f568])).

fof(f177,plain,
    ( spl2_11
  <=> u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f182,plain,
    ( spl2_12
  <=> u1_pre_topc(sK1) = k2_tarski(k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f475,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | ~ spl2_11
    | spl2_12
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f456,f179])).

fof(f179,plain,
    ( u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f177])).

fof(f456,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | spl2_12
    | ~ spl2_24 ),
    inference(superposition,[],[f184,f426])).

fof(f184,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK1))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f560,plain,
    ( spl2_31
    | ~ spl2_2
    | ~ spl2_19
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f510,f502,f299,f81,f557])).

fof(f299,plain,
    ( spl2_19
  <=> m1_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f510,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ spl2_2
    | ~ spl2_19
    | ~ spl2_30 ),
    inference(unit_resulting_resolution,[],[f301,f504,f310])).

fof(f310,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | v1_tops_2(u1_pre_topc(sK1),X1)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl2_2 ),
    inference(resolution,[],[f203,f83])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | v1_tops_2(u1_pre_topc(X0),X1)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | v1_tops_2(u1_pre_topc(X0),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f133,f73])).

fof(f73,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_tops_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f70,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

fof(f133,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f132,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
      | v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
      | v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f61,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f301,plain,
    ( m1_pre_topc(sK0,sK1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f299])).

fof(f505,plain,
    ( spl2_30
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f353,f312,f143,f76,f502])).

fof(f143,plain,
    ( spl2_8
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f312,plain,
    ( spl2_20
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f353,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f145,f78,f314,f222])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X2)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f219,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f139,f59])).

fof(f139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f138,f57])).

fof(f138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f59,f51])).

fof(f314,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f312])).

fof(f145,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f500,plain,
    ( spl2_29
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_20
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f483,f424,f312,f167,f76,f497])).

fof(f483,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_20
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f482,f314])).

fof(f482,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f473,f169])).

fof(f473,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_24 ),
    inference(superposition,[],[f309,f426])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f203,f78])).

fof(f427,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f355,f312,f299,f76,f424])).

fof(f355,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_1
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f78,f301,f314,f227])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f225,f57])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f115,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(resolution,[],[f58,f69])).

fof(f315,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f263,f247,f76,f312])).

fof(f247,plain,
    ( spl2_16
  <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f263,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f78,f249,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f249,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f247])).

fof(f302,plain,
    ( spl2_19
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f251,f242,f107,f81,f299])).

fof(f107,plain,
    ( spl2_6
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f242,plain,
    ( spl2_15
  <=> m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f251,plain,
    ( m1_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f244,f126])).

fof(f126,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | m1_pre_topc(X1,sK1) )
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f125,f109])).

fof(f109,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f125,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_pre_topc(X1,sK1) )
    | ~ spl2_2 ),
    inference(resolution,[],[f63,f83])).

fof(f244,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f242])).

fof(f250,plain,
    ( spl2_16
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f165,f143,f107,f81,f247])).

fof(f165,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f159,f109])).

fof(f159,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f83,f83,f145,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f245,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f147,f98,f76,f242])).

fof(f98,plain,
    ( spl2_5
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f147,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f78,f78,f100,f55])).

fof(f100,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f185,plain,
    ( ~ spl2_12
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f123,f91,f81,f182])).

fof(f91,plain,
    ( spl2_4
  <=> v2_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f123,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK1))
    | ~ spl2_2
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f83,f93,f54])).

fof(f54,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

fof(f93,plain,
    ( ~ v2_tdlat_3(sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f180,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f116,f86,f76,f177])).

fof(f86,plain,
    ( spl2_3
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f116,plain,
    ( u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f78,f88,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f170,plain,
    ( spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f111,f76,f167])).

fof(f111,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f78,f51])).

fof(f146,plain,
    ( spl2_8
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f96,f81,f143])).

fof(f96,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f83,f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f110,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f47,f107])).

fof(f47,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ v2_tdlat_3(sK1)
    & v2_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tdlat_3(X1)
            & v2_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ~ v2_tdlat_3(X1)
        & v2_tdlat_3(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v2_tdlat_3(sK1)
      & v2_tdlat_3(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

fof(f101,plain,
    ( spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f95,f76,f98])).

fof(f95,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f78,f50])).

fof(f94,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f49,f91])).

fof(f49,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f48,f86])).

fof(f48,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f45,f76])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (8532)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.47  % (8516)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.47  % (8516)Refutation not found, incomplete strategy% (8516)------------------------------
% 0.21/0.47  % (8516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8516)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (8516)Memory used [KB]: 1663
% 0.21/0.47  % (8516)Time elapsed: 0.054 s
% 0.21/0.47  % (8516)------------------------------
% 0.21/0.47  % (8516)------------------------------
% 0.21/0.48  % (8510)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (8532)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f668,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f101,f110,f146,f170,f180,f185,f245,f250,f302,f315,f427,f500,f505,f560,f571,f600,f641,f667])).
% 0.21/0.49  fof(f667,plain,(
% 0.21/0.49    spl2_32 | ~spl2_33 | ~spl2_34),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f666])).
% 0.21/0.49  fof(f666,plain,(
% 0.21/0.49    $false | (spl2_32 | ~spl2_33 | ~spl2_34)),
% 0.21/0.49    inference(subsumption_resolution,[],[f665,f570])).
% 0.21/0.49  fof(f570,plain,(
% 0.21/0.49    u1_pre_topc(sK0) != u1_pre_topc(sK1) | spl2_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f568])).
% 0.21/0.49  fof(f568,plain,(
% 0.21/0.49    spl2_32 <=> u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.49  fof(f665,plain,(
% 0.21/0.49    u1_pre_topc(sK0) = u1_pre_topc(sK1) | (~spl2_33 | ~spl2_34)),
% 0.21/0.49    inference(subsumption_resolution,[],[f660,f640])).
% 0.21/0.49  fof(f640,plain,(
% 0.21/0.49    r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl2_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f638])).
% 0.21/0.49  fof(f638,plain,(
% 0.21/0.49    spl2_34 <=> r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.49  fof(f660,plain,(
% 0.21/0.49    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~spl2_33),
% 0.21/0.49    inference(resolution,[],[f599,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f599,plain,(
% 0.21/0.49    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~spl2_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f597])).
% 0.21/0.49  fof(f597,plain,(
% 0.21/0.49    spl2_33 <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.49  fof(f641,plain,(
% 0.21/0.49    spl2_34 | ~spl2_1 | ~spl2_30 | ~spl2_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f563,f557,f502,f76,f638])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl2_1 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f502,plain,(
% 0.21/0.49    spl2_30 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.49  fof(f557,plain,(
% 0.21/0.49    spl2_31 <=> v1_tops_2(u1_pre_topc(sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.49  fof(f563,plain,(
% 0.21/0.49    r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | (~spl2_1 | ~spl2_30 | ~spl2_31)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f504,f559,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_tops_2(X1,X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.21/0.49  fof(f559,plain,(
% 0.21/0.49    v1_tops_2(u1_pre_topc(sK1),sK0) | ~spl2_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f557])).
% 0.21/0.49  fof(f504,plain,(
% 0.21/0.49    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f502])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f600,plain,(
% 0.21/0.49    spl2_33 | ~spl2_2 | ~spl2_9 | ~spl2_24 | ~spl2_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f555,f497,f424,f167,f81,f597])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl2_2 <=> l1_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    spl2_9 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.49  fof(f424,plain,(
% 0.21/0.49    spl2_24 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.49  fof(f497,plain,(
% 0.21/0.49    spl2_29 <=> v1_tops_2(u1_pre_topc(sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.49  fof(f555,plain,(
% 0.21/0.49    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | (~spl2_2 | ~spl2_9 | ~spl2_24 | ~spl2_29)),
% 0.21/0.49    inference(subsumption_resolution,[],[f554,f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f167])).
% 0.21/0.49  fof(f554,plain,(
% 0.21/0.49    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | (~spl2_2 | ~spl2_24 | ~spl2_29)),
% 0.21/0.49    inference(forward_demodulation,[],[f553,f426])).
% 0.21/0.49  fof(f426,plain,(
% 0.21/0.49    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl2_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f424])).
% 0.21/0.49  fof(f553,plain,(
% 0.21/0.49    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl2_2 | ~spl2_29)),
% 0.21/0.49    inference(subsumption_resolution,[],[f551,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    l1_pre_topc(sK1) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f551,plain,(
% 0.21/0.49    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~spl2_29),
% 0.21/0.49    inference(resolution,[],[f499,f60])).
% 0.21/0.49  fof(f499,plain,(
% 0.21/0.49    v1_tops_2(u1_pre_topc(sK0),sK1) | ~spl2_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f497])).
% 0.21/0.49  fof(f571,plain,(
% 0.21/0.49    ~spl2_32 | ~spl2_11 | spl2_12 | ~spl2_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f475,f424,f182,f177,f568])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl2_11 <=> u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl2_12 <=> u1_pre_topc(sK1) = k2_tarski(k1_xboole_0,u1_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.49  fof(f475,plain,(
% 0.21/0.49    u1_pre_topc(sK0) != u1_pre_topc(sK1) | (~spl2_11 | spl2_12 | ~spl2_24)),
% 0.21/0.49    inference(forward_demodulation,[],[f456,f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f177])).
% 0.21/0.49  fof(f456,plain,(
% 0.21/0.49    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | (spl2_12 | ~spl2_24)),
% 0.21/0.49    inference(superposition,[],[f184,f426])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK1)) | spl2_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f182])).
% 0.21/0.49  fof(f560,plain,(
% 0.21/0.49    spl2_31 | ~spl2_2 | ~spl2_19 | ~spl2_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f510,f502,f299,f81,f557])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    spl2_19 <=> m1_pre_topc(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.49  fof(f510,plain,(
% 0.21/0.49    v1_tops_2(u1_pre_topc(sK1),sK0) | (~spl2_2 | ~spl2_19 | ~spl2_30)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f301,f504,f310])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | v1_tops_2(u1_pre_topc(sK1),X1) | ~m1_pre_topc(X1,sK1)) ) | ~spl2_2),
% 0.21/0.49    inference(resolution,[],[f203,f83])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | v1_tops_2(u1_pre_topc(X0),X1) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f200])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | v1_tops_2(u1_pre_topc(X0),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f133,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (~v1_tops_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f132,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) | v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) | v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f61,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    m1_pre_topc(sK0,sK1) | ~spl2_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f299])).
% 0.21/0.49  fof(f505,plain,(
% 0.21/0.49    spl2_30 | ~spl2_1 | ~spl2_8 | ~spl2_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f353,f312,f143,f76,f502])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl2_8 <=> m1_pre_topc(sK1,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    spl2_20 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl2_1 | ~spl2_8 | ~spl2_20)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f145,f78,f314,f222])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f219,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.49    inference(resolution,[],[f139,f59])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f138,f57])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f59,f51])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK0) | ~spl2_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f312])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK1) | ~spl2_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f500,plain,(
% 0.21/0.49    spl2_29 | ~spl2_1 | ~spl2_9 | ~spl2_20 | ~spl2_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f483,f424,f312,f167,f76,f497])).
% 0.21/0.49  fof(f483,plain,(
% 0.21/0.49    v1_tops_2(u1_pre_topc(sK0),sK1) | (~spl2_1 | ~spl2_9 | ~spl2_20 | ~spl2_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f482,f314])).
% 0.21/0.49  fof(f482,plain,(
% 0.21/0.49    v1_tops_2(u1_pre_topc(sK0),sK1) | ~m1_pre_topc(sK1,sK0) | (~spl2_1 | ~spl2_9 | ~spl2_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f473,f169])).
% 0.21/0.49  fof(f473,plain,(
% 0.21/0.49    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(u1_pre_topc(sK0),sK1) | ~m1_pre_topc(sK1,sK0) | (~spl2_1 | ~spl2_24)),
% 0.21/0.49    inference(superposition,[],[f309,f426])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(u1_pre_topc(sK0),X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl2_1),
% 0.21/0.49    inference(resolution,[],[f203,f78])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    spl2_24 | ~spl2_1 | ~spl2_19 | ~spl2_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f355,f312,f299,f76,f424])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    u1_struct_0(sK0) = u1_struct_0(sK1) | (~spl2_1 | ~spl2_19 | ~spl2_20)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f301,f314,f227])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X1) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f225,f57])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.49    inference(resolution,[],[f115,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | u1_struct_0(X0) = u1_struct_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f58,f69])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    spl2_20 | ~spl2_1 | ~spl2_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f263,f247,f76,f312])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    spl2_16 <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK0) | (~spl2_1 | ~spl2_16)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f249,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f247])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    spl2_19 | ~spl2_2 | ~spl2_6 | ~spl2_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f251,f242,f107,f81,f299])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl2_6 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    spl2_15 <=> m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    m1_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_6 | ~spl2_15)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f244,f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X1,sK1)) ) | (~spl2_2 | ~spl2_6)),
% 0.21/0.49    inference(forward_demodulation,[],[f125,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X1,sK1)) ) | ~spl2_2),
% 0.21/0.49    inference(resolution,[],[f63,f83])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f242])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    spl2_16 | ~spl2_2 | ~spl2_6 | ~spl2_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f165,f143,f107,f81,f247])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_2 | ~spl2_6 | ~spl2_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f159,f109])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl2_2 | ~spl2_8)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f83,f83,f145,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    spl2_15 | ~spl2_1 | ~spl2_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f147,f98,f76,f242])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl2_5 <=> m1_pre_topc(sK0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_1 | ~spl2_5)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f78,f100,f55])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    m1_pre_topc(sK0,sK0) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f98])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    ~spl2_12 | ~spl2_2 | spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f123,f91,f81,f182])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl2_4 <=> v2_tdlat_3(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK1)) | (~spl2_2 | spl2_4)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f83,f93,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) | v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0] : (((v2_tdlat_3(X0) | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))) & (u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~v2_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : ((v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~v2_tdlat_3(sK1) | spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl2_11 | ~spl2_1 | ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f116,f86,f76,f177])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl2_3 <=> v2_tdlat_3(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | (~spl2_1 | ~spl2_3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f88,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_tdlat_3(X0) | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    v2_tdlat_3(sK0) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl2_9 | ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f111,f76,f167])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_1),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f51])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl2_8 | ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f96,f81,f143])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK1) | ~spl2_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f83,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f107])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    (~v2_tdlat_3(sK1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f37,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) => (~v2_tdlat_3(sK1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((~v2_tdlat_3(X1) & (v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f15])).
% 0.21/0.49  fof(f15,conjecture,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl2_5 | ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f95,f76,f98])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    m1_pre_topc(sK0,sK0) | ~spl2_1),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f50])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f91])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ~v2_tdlat_3(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f86])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    v2_tdlat_3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f81])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    l1_pre_topc(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f76])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (8532)------------------------------
% 0.21/0.49  % (8532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8532)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (8532)Memory used [KB]: 10874
% 0.21/0.49  % (8532)Time elapsed: 0.070 s
% 0.21/0.49  % (8532)------------------------------
% 0.21/0.49  % (8532)------------------------------
% 0.21/0.49  % (8508)Success in time 0.127 s
%------------------------------------------------------------------------------
