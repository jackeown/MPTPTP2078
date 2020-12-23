%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:34 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 436 expanded)
%              Number of leaves         :   32 ( 133 expanded)
%              Depth                    :   17
%              Number of atoms          :  504 (2097 expanded)
%              Number of equality atoms :   77 ( 516 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f151,f175,f183,f185,f236,f1361,f1366,f1388,f1424,f1444,f1463,f1471,f1478])).

fof(f1478,plain,(
    spl5_98 ),
    inference(avatar_contradiction_clause,[],[f1475])).

fof(f1475,plain,
    ( $false
    | spl5_98 ),
    inference(resolution,[],[f1467,f135])).

fof(f135,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1467,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl5_98 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1466,plain,
    ( spl5_98
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f1471,plain,
    ( ~ spl5_98
    | spl5_23
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f1470,f143,f296,f1466])).

fof(f296,plain,
    ( spl5_23
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f143,plain,
    ( spl5_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1470,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(global_subsumption,[],[f272])).

fof(f272,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f160,f71])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | r1_tarski(X0,k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(global_subsumption,[],[f70,f152])).

fof(f152,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ v3_pre_topc(X0,sK0)
      | r1_tarski(X0,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f71,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f1463,plain,
    ( ~ spl5_6
    | spl5_2
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f1436,f299,f146,f213])).

fof(f213,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f146,plain,
    ( spl5_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f299,plain,
    ( spl5_24
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1436,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f1428,f300])).

fof(f300,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f299])).

fof(f1428,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f71,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1444,plain,(
    spl5_93 ),
    inference(avatar_contradiction_clause,[],[f1443])).

fof(f1443,plain,
    ( $false
    | spl5_93 ),
    inference(subsumption_resolution,[],[f69,f1387])).

fof(f1387,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_93 ),
    inference(avatar_component_clause,[],[f1386])).

fof(f1386,plain,
    ( spl5_93
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f1424,plain,(
    spl5_37 ),
    inference(avatar_contradiction_clause,[],[f1423])).

fof(f1423,plain,
    ( $false
    | spl5_37 ),
    inference(subsumption_resolution,[],[f71,f500])).

fof(f500,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl5_37
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f1388,plain,
    ( ~ spl5_93
    | ~ spl5_6
    | ~ spl5_37
    | spl5_1
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f1382,f299,f143,f499,f213,f1386])).

fof(f1382,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_24 ),
    inference(superposition,[],[f90,f300])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f1366,plain,
    ( spl5_24
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f474,f296,f299])).

fof(f474,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(superposition,[],[f265,f162])).

fof(f162,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f70,f154])).

fof(f154,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f71,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f265,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))
      | sK1 = k7_subset_1(u1_struct_0(sK0),sK1,X0) ) ),
    inference(resolution,[],[f203,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f203,plain,(
    ! [X6] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X6),sK1) ),
    inference(superposition,[],[f118,f157])).

fof(f157,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1))) ),
    inference(resolution,[],[f71,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f99,f113])).

fof(f113,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f86,f84])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f118,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f82,f113])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1361,plain,
    ( ~ spl5_2
    | ~ spl5_5
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f1358])).

fof(f1358,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5
    | spl5_23 ),
    inference(subsumption_resolution,[],[f297,f1356])).

fof(f1356,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f1352])).

fof(f1352,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(resolution,[],[f1346,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1346,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2(X2,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X2,k1_tops_1(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(resolution,[],[f1309,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1309,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f338,f1272])).

fof(f1272,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f594,f150])).

fof(f150,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f146])).

fof(f594,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2))
        | ~ r2_hidden(X3,X2) )
    | ~ spl5_5 ),
    inference(superposition,[],[f140,f242])).

fof(f242,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X1)))
    | ~ spl5_5 ),
    inference(resolution,[],[f182,f121])).

fof(f182,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl5_5
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f140,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f108,f113])).

fof(f108,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f338,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tops_1(sK0,sK1))
      | r2_hidden(X0,k2_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f202,f162])).

fof(f202,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,k7_subset_1(u1_struct_0(sK0),sK1,X4))
      | r2_hidden(X5,X4)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(superposition,[],[f139,f157])).

fof(f139,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f109,f113])).

fof(f109,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f297,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f296])).

fof(f236,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f70,f214])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f213])).

fof(f185,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f71,f176])).

fof(f176,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3 ),
    inference(resolution,[],[f171,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f171,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_3
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f183,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f178,f181,f173])).

fof(f173,plain,
    ( spl5_4
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f178,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f71,f177])).

fof(f177,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f100,f163])).

fof(f163,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f70,f155])).

fof(f155,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f71,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f175,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f168,f173,f170])).

fof(f168,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f70,f167])).

fof(f167,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f91,f164])).

fof(f164,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(global_subsumption,[],[f70,f156])).

fof(f156,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f71,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f151,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f72,f146,f143])).

fof(f72,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f148,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f73,f146,f143])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (27249)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.48  % (27257)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (27246)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (27261)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (27254)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (27239)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (27238)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (27263)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.59  % (27253)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.59  % (27237)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.59  % (27245)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.59  % (27253)Refutation not found, incomplete strategy% (27253)------------------------------
% 0.21/0.59  % (27253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.59  % (27241)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.82/0.60  % (27247)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.82/0.60  % (27253)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.60  
% 1.82/0.60  % (27253)Memory used [KB]: 10618
% 1.82/0.60  % (27253)Time elapsed: 0.153 s
% 1.82/0.60  % (27253)------------------------------
% 1.82/0.60  % (27253)------------------------------
% 1.82/0.60  % (27252)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.82/0.60  % (27236)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.82/0.60  % (27250)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.95/0.61  % (27258)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.95/0.62  % (27240)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.95/0.62  % (27260)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.95/0.62  % (27243)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.95/0.63  % (27256)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.95/0.63  % (27244)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.95/0.63  % (27264)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.95/0.64  % (27265)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.95/0.64  % (27251)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.95/0.64  % (27262)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.95/0.64  % (27255)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.95/0.64  % (27248)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.19/0.64  % (27258)Refutation not found, incomplete strategy% (27258)------------------------------
% 2.19/0.64  % (27258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.64  % (27258)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.64  
% 2.19/0.64  % (27258)Memory used [KB]: 10746
% 2.19/0.64  % (27258)Time elapsed: 0.163 s
% 2.19/0.64  % (27258)------------------------------
% 2.19/0.64  % (27258)------------------------------
% 2.19/0.64  % (27242)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.19/0.65  % (27259)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.19/0.68  % (27238)Refutation found. Thanks to Tanya!
% 2.19/0.68  % SZS status Theorem for theBenchmark
% 2.19/0.68  % SZS output start Proof for theBenchmark
% 2.19/0.68  fof(f1479,plain,(
% 2.19/0.68    $false),
% 2.19/0.68    inference(avatar_sat_refutation,[],[f148,f151,f175,f183,f185,f236,f1361,f1366,f1388,f1424,f1444,f1463,f1471,f1478])).
% 2.19/0.68  fof(f1478,plain,(
% 2.19/0.68    spl5_98),
% 2.19/0.68    inference(avatar_contradiction_clause,[],[f1475])).
% 2.19/0.68  fof(f1475,plain,(
% 2.19/0.68    $false | spl5_98),
% 2.19/0.68    inference(resolution,[],[f1467,f135])).
% 2.19/0.68  fof(f135,plain,(
% 2.19/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.19/0.68    inference(equality_resolution,[],[f92])).
% 2.19/0.68  fof(f92,plain,(
% 2.19/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.19/0.68    inference(cnf_transformation,[],[f54])).
% 2.19/0.68  fof(f54,plain,(
% 2.19/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.68    inference(flattening,[],[f53])).
% 2.19/0.68  fof(f53,plain,(
% 2.19/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.68    inference(nnf_transformation,[],[f5])).
% 2.19/0.68  fof(f5,axiom,(
% 2.19/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.19/0.68  fof(f1467,plain,(
% 2.19/0.68    ~r1_tarski(sK1,sK1) | spl5_98),
% 2.19/0.68    inference(avatar_component_clause,[],[f1466])).
% 2.19/0.68  fof(f1466,plain,(
% 2.19/0.68    spl5_98 <=> r1_tarski(sK1,sK1)),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 2.19/0.68  fof(f1471,plain,(
% 2.19/0.68    ~spl5_98 | spl5_23 | ~spl5_1),
% 2.19/0.68    inference(avatar_split_clause,[],[f1470,f143,f296,f1466])).
% 2.19/0.68  fof(f296,plain,(
% 2.19/0.68    spl5_23 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.19/0.68  fof(f143,plain,(
% 2.19/0.68    spl5_1 <=> v3_pre_topc(sK1,sK0)),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.19/0.68  fof(f1470,plain,(
% 2.19/0.68    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1)),
% 2.19/0.68    inference(global_subsumption,[],[f272])).
% 2.19/0.68  fof(f272,plain,(
% 2.19/0.68    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1)),
% 2.19/0.68    inference(resolution,[],[f160,f71])).
% 2.19/0.68  fof(f71,plain,(
% 2.19/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.68    inference(cnf_transformation,[],[f52])).
% 2.19/0.68  fof(f52,plain,(
% 2.19/0.68    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.19/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 2.19/0.68  fof(f50,plain,(
% 2.19/0.68    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.19/0.68    introduced(choice_axiom,[])).
% 2.19/0.68  fof(f51,plain,(
% 2.19/0.68    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.19/0.68    introduced(choice_axiom,[])).
% 2.19/0.68  fof(f49,plain,(
% 2.19/0.68    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/0.68    inference(flattening,[],[f48])).
% 2.19/0.68  fof(f48,plain,(
% 2.19/0.68    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/0.68    inference(nnf_transformation,[],[f30])).
% 2.19/0.68  fof(f30,plain,(
% 2.19/0.68    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/0.68    inference(flattening,[],[f29])).
% 2.19/0.68  fof(f29,plain,(
% 2.19/0.68    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.19/0.68    inference(ennf_transformation,[],[f27])).
% 2.19/0.68  fof(f27,negated_conjecture,(
% 2.19/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.19/0.68    inference(negated_conjecture,[],[f26])).
% 2.19/0.68  fof(f26,conjecture,(
% 2.19/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.19/0.68  fof(f160,plain,(
% 2.19/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1)) )),
% 2.19/0.68    inference(global_subsumption,[],[f70,f152])).
% 2.19/0.68  fof(f152,plain,(
% 2.19/0.68    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.19/0.68    inference(resolution,[],[f71,f80])).
% 2.19/0.68  fof(f80,plain,(
% 2.19/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f36])).
% 2.19/0.68  fof(f36,plain,(
% 2.19/0.68    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.68    inference(flattening,[],[f35])).
% 2.19/0.68  fof(f35,plain,(
% 2.19/0.68    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.68    inference(ennf_transformation,[],[f22])).
% 2.19/0.68  fof(f22,axiom,(
% 2.19/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 2.19/0.68  fof(f70,plain,(
% 2.19/0.68    l1_pre_topc(sK0)),
% 2.19/0.68    inference(cnf_transformation,[],[f52])).
% 2.19/0.68  fof(f1463,plain,(
% 2.19/0.68    ~spl5_6 | spl5_2 | ~spl5_24),
% 2.19/0.68    inference(avatar_split_clause,[],[f1436,f299,f146,f213])).
% 2.19/0.68  fof(f213,plain,(
% 2.19/0.68    spl5_6 <=> l1_pre_topc(sK0)),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.19/0.68  fof(f146,plain,(
% 2.19/0.68    spl5_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.19/0.68  fof(f299,plain,(
% 2.19/0.68    spl5_24 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 2.19/0.68  fof(f1436,plain,(
% 2.19/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl5_24),
% 2.19/0.68    inference(forward_demodulation,[],[f1428,f300])).
% 2.19/0.68  fof(f300,plain,(
% 2.19/0.68    sK1 = k1_tops_1(sK0,sK1) | ~spl5_24),
% 2.19/0.68    inference(avatar_component_clause,[],[f299])).
% 2.19/0.68  fof(f1428,plain,(
% 2.19/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.19/0.68    inference(resolution,[],[f71,f79])).
% 2.19/0.68  fof(f79,plain,(
% 2.19/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f34])).
% 2.19/0.68  fof(f34,plain,(
% 2.19/0.68    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.68    inference(ennf_transformation,[],[f21])).
% 2.19/0.68  fof(f21,axiom,(
% 2.19/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.19/0.68  fof(f1444,plain,(
% 2.19/0.68    spl5_93),
% 2.19/0.68    inference(avatar_contradiction_clause,[],[f1443])).
% 2.19/0.68  fof(f1443,plain,(
% 2.19/0.68    $false | spl5_93),
% 2.19/0.68    inference(subsumption_resolution,[],[f69,f1387])).
% 2.19/0.68  fof(f1387,plain,(
% 2.19/0.68    ~v2_pre_topc(sK0) | spl5_93),
% 2.19/0.68    inference(avatar_component_clause,[],[f1386])).
% 2.19/0.68  fof(f1386,plain,(
% 2.19/0.68    spl5_93 <=> v2_pre_topc(sK0)),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 2.19/0.68  fof(f69,plain,(
% 2.19/0.68    v2_pre_topc(sK0)),
% 2.19/0.68    inference(cnf_transformation,[],[f52])).
% 2.19/0.68  fof(f1424,plain,(
% 2.19/0.68    spl5_37),
% 2.19/0.68    inference(avatar_contradiction_clause,[],[f1423])).
% 2.19/0.68  fof(f1423,plain,(
% 2.19/0.68    $false | spl5_37),
% 2.19/0.68    inference(subsumption_resolution,[],[f71,f500])).
% 2.19/0.68  fof(f500,plain,(
% 2.19/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_37),
% 2.19/0.68    inference(avatar_component_clause,[],[f499])).
% 2.19/0.68  fof(f499,plain,(
% 2.19/0.68    spl5_37 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.19/0.68  fof(f1388,plain,(
% 2.19/0.68    ~spl5_93 | ~spl5_6 | ~spl5_37 | spl5_1 | ~spl5_24),
% 2.19/0.68    inference(avatar_split_clause,[],[f1382,f299,f143,f499,f213,f1386])).
% 2.19/0.68  fof(f1382,plain,(
% 2.19/0.68    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl5_24),
% 2.19/0.68    inference(superposition,[],[f90,f300])).
% 2.19/0.68  fof(f90,plain,(
% 2.19/0.68    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f41])).
% 2.19/0.68  fof(f41,plain,(
% 2.19/0.68    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.19/0.68    inference(flattening,[],[f40])).
% 2.19/0.68  fof(f40,plain,(
% 2.19/0.68    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.19/0.68    inference(ennf_transformation,[],[f20])).
% 2.19/0.68  fof(f20,axiom,(
% 2.19/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.19/0.68  fof(f1366,plain,(
% 2.19/0.68    spl5_24 | ~spl5_23),
% 2.19/0.68    inference(avatar_split_clause,[],[f474,f296,f299])).
% 2.19/0.68  fof(f474,plain,(
% 2.19/0.68    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 2.19/0.68    inference(superposition,[],[f265,f162])).
% 2.19/0.68  fof(f162,plain,(
% 2.19/0.68    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.19/0.68    inference(global_subsumption,[],[f70,f154])).
% 2.19/0.68  fof(f154,plain,(
% 2.19/0.68    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.19/0.68    inference(resolution,[],[f71,f78])).
% 2.19/0.68  fof(f78,plain,(
% 2.19/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f33])).
% 2.19/0.68  fof(f33,plain,(
% 2.19/0.68    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.68    inference(ennf_transformation,[],[f25])).
% 2.19/0.68  fof(f25,axiom,(
% 2.19/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.19/0.68  fof(f265,plain,(
% 2.19/0.68    ( ! [X0] : (~r1_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) | sK1 = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 2.19/0.68    inference(resolution,[],[f203,f94])).
% 2.19/0.68  fof(f94,plain,(
% 2.19/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f54])).
% 2.19/0.68  fof(f203,plain,(
% 2.19/0.68    ( ! [X6] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X6),sK1)) )),
% 2.19/0.68    inference(superposition,[],[f118,f157])).
% 2.19/0.68  fof(f157,plain,(
% 2.19/0.68    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1)))) )),
% 2.19/0.68    inference(resolution,[],[f71,f121])).
% 2.19/0.68  fof(f121,plain,(
% 2.19/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 2.19/0.68    inference(definition_unfolding,[],[f99,f113])).
% 2.19/0.68  fof(f113,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.19/0.68    inference(definition_unfolding,[],[f86,f84])).
% 2.19/0.68  fof(f84,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f18])).
% 2.19/0.68  fof(f18,axiom,(
% 2.19/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.19/0.68  fof(f86,plain,(
% 2.19/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f6])).
% 2.19/0.68  fof(f6,axiom,(
% 2.19/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.19/0.68  fof(f99,plain,(
% 2.19/0.68    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f45])).
% 2.19/0.68  fof(f45,plain,(
% 2.19/0.68    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.68    inference(ennf_transformation,[],[f17])).
% 2.19/0.68  fof(f17,axiom,(
% 2.19/0.68    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.19/0.68  fof(f118,plain,(
% 2.19/0.68    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.19/0.68    inference(definition_unfolding,[],[f82,f113])).
% 2.19/0.68  fof(f82,plain,(
% 2.19/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f9])).
% 2.19/0.68  fof(f9,axiom,(
% 2.19/0.68    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.19/0.68  fof(f1361,plain,(
% 2.19/0.68    ~spl5_2 | ~spl5_5 | spl5_23),
% 2.19/0.68    inference(avatar_contradiction_clause,[],[f1358])).
% 2.19/0.68  fof(f1358,plain,(
% 2.19/0.68    $false | (~spl5_2 | ~spl5_5 | spl5_23)),
% 2.19/0.68    inference(subsumption_resolution,[],[f297,f1356])).
% 2.19/0.68  fof(f1356,plain,(
% 2.19/0.68    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl5_2 | ~spl5_5)),
% 2.19/0.68    inference(duplicate_literal_removal,[],[f1352])).
% 2.19/0.68  fof(f1352,plain,(
% 2.19/0.68    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl5_2 | ~spl5_5)),
% 2.19/0.68    inference(resolution,[],[f1346,f96])).
% 2.19/0.68  fof(f96,plain,(
% 2.19/0.68    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f58])).
% 2.19/0.68  fof(f58,plain,(
% 2.19/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.19/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).
% 2.19/0.68  fof(f57,plain,(
% 2.19/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.19/0.68    introduced(choice_axiom,[])).
% 2.19/0.68  fof(f56,plain,(
% 2.19/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.19/0.68    inference(rectify,[],[f55])).
% 2.19/0.68  fof(f55,plain,(
% 2.19/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.19/0.68    inference(nnf_transformation,[],[f44])).
% 2.19/0.68  fof(f44,plain,(
% 2.19/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.19/0.68    inference(ennf_transformation,[],[f1])).
% 2.19/0.68  fof(f1,axiom,(
% 2.19/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.19/0.68  fof(f1346,plain,(
% 2.19/0.68    ( ! [X2] : (~r2_hidden(sK2(X2,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X2,k1_tops_1(sK0,sK1))) ) | (~spl5_2 | ~spl5_5)),
% 2.19/0.68    inference(resolution,[],[f1309,f97])).
% 2.19/0.68  fof(f97,plain,(
% 2.19/0.68    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f58])).
% 2.19/0.68  fof(f1309,plain,(
% 2.19/0.68    ( ! [X0] : (r2_hidden(X0,k1_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | (~spl5_2 | ~spl5_5)),
% 2.19/0.68    inference(subsumption_resolution,[],[f338,f1272])).
% 2.19/0.68  fof(f1272,plain,(
% 2.19/0.68    ( ! [X0] : (~r2_hidden(X0,k2_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | (~spl5_2 | ~spl5_5)),
% 2.19/0.68    inference(superposition,[],[f594,f150])).
% 2.19/0.68  fof(f150,plain,(
% 2.19/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl5_2),
% 2.19/0.68    inference(avatar_component_clause,[],[f146])).
% 2.19/0.68  fof(f594,plain,(
% 2.19/0.68    ( ! [X2,X3] : (~r2_hidden(X3,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2)) | ~r2_hidden(X3,X2)) ) | ~spl5_5),
% 2.19/0.68    inference(superposition,[],[f140,f242])).
% 2.19/0.68  fof(f242,plain,(
% 2.19/0.68    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X1)))) ) | ~spl5_5),
% 2.19/0.68    inference(resolution,[],[f182,f121])).
% 2.19/0.68  fof(f182,plain,(
% 2.19/0.68    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 2.19/0.68    inference(avatar_component_clause,[],[f181])).
% 2.19/0.68  fof(f181,plain,(
% 2.19/0.68    spl5_5 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.19/0.68  fof(f140,plain,(
% 2.19/0.68    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | ~r2_hidden(X4,X1)) )),
% 2.19/0.68    inference(equality_resolution,[],[f132])).
% 2.19/0.68  fof(f132,plain,(
% 2.19/0.68    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.19/0.68    inference(definition_unfolding,[],[f108,f113])).
% 2.19/0.68  fof(f108,plain,(
% 2.19/0.68    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.19/0.68    inference(cnf_transformation,[],[f68])).
% 2.19/0.68  fof(f68,plain,(
% 2.19/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.19/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f66,f67])).
% 2.19/0.68  fof(f67,plain,(
% 2.19/0.68    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.19/0.68    introduced(choice_axiom,[])).
% 2.19/0.68  fof(f66,plain,(
% 2.19/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.19/0.68    inference(rectify,[],[f65])).
% 2.19/0.68  fof(f65,plain,(
% 2.19/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.19/0.68    inference(flattening,[],[f64])).
% 2.19/0.68  fof(f64,plain,(
% 2.19/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.19/0.68    inference(nnf_transformation,[],[f3])).
% 2.19/0.68  fof(f3,axiom,(
% 2.19/0.68    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.19/0.68  fof(f338,plain,(
% 2.19/0.68    ( ! [X0] : (r2_hidden(X0,k1_tops_1(sK0,sK1)) | r2_hidden(X0,k2_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 2.19/0.68    inference(superposition,[],[f202,f162])).
% 2.19/0.68  fof(f202,plain,(
% 2.19/0.68    ( ! [X4,X5] : (r2_hidden(X5,k7_subset_1(u1_struct_0(sK0),sK1,X4)) | r2_hidden(X5,X4) | ~r2_hidden(X5,sK1)) )),
% 2.19/0.68    inference(superposition,[],[f139,f157])).
% 2.19/0.68  fof(f139,plain,(
% 2.19/0.68    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.19/0.68    inference(equality_resolution,[],[f131])).
% 2.19/0.68  fof(f131,plain,(
% 2.19/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.19/0.68    inference(definition_unfolding,[],[f109,f113])).
% 2.19/0.68  fof(f109,plain,(
% 2.19/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.19/0.68    inference(cnf_transformation,[],[f68])).
% 2.19/0.68  fof(f297,plain,(
% 2.19/0.68    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl5_23),
% 2.19/0.68    inference(avatar_component_clause,[],[f296])).
% 2.19/0.68  fof(f236,plain,(
% 2.19/0.68    spl5_6),
% 2.19/0.68    inference(avatar_contradiction_clause,[],[f235])).
% 2.19/0.68  fof(f235,plain,(
% 2.19/0.68    $false | spl5_6),
% 2.19/0.68    inference(subsumption_resolution,[],[f70,f214])).
% 2.19/0.68  fof(f214,plain,(
% 2.19/0.68    ~l1_pre_topc(sK0) | spl5_6),
% 2.19/0.68    inference(avatar_component_clause,[],[f213])).
% 2.19/0.68  fof(f185,plain,(
% 2.19/0.68    spl5_3),
% 2.19/0.68    inference(avatar_contradiction_clause,[],[f184])).
% 2.19/0.68  fof(f184,plain,(
% 2.19/0.68    $false | spl5_3),
% 2.19/0.68    inference(subsumption_resolution,[],[f71,f176])).
% 2.19/0.68  fof(f176,plain,(
% 2.19/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_3),
% 2.19/0.68    inference(resolution,[],[f171,f87])).
% 2.19/0.68  fof(f87,plain,(
% 2.19/0.68    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f37])).
% 2.19/0.68  fof(f37,plain,(
% 2.19/0.68    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.68    inference(ennf_transformation,[],[f14])).
% 2.19/0.68  fof(f14,axiom,(
% 2.19/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.19/0.68  fof(f171,plain,(
% 2.19/0.68    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_3),
% 2.19/0.68    inference(avatar_component_clause,[],[f170])).
% 2.19/0.68  fof(f170,plain,(
% 2.19/0.68    spl5_3 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.19/0.68  fof(f183,plain,(
% 2.19/0.68    ~spl5_4 | spl5_5),
% 2.19/0.68    inference(avatar_split_clause,[],[f178,f181,f173])).
% 2.19/0.68  fof(f173,plain,(
% 2.19/0.68    spl5_4 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.19/0.68  fof(f178,plain,(
% 2.19/0.68    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.68    inference(global_subsumption,[],[f71,f177])).
% 2.19/0.68  fof(f177,plain,(
% 2.19/0.68    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.68    inference(superposition,[],[f100,f163])).
% 2.19/0.68  fof(f163,plain,(
% 2.19/0.68    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.19/0.68    inference(global_subsumption,[],[f70,f155])).
% 2.19/0.68  fof(f155,plain,(
% 2.19/0.68    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.19/0.68    inference(resolution,[],[f71,f77])).
% 2.19/0.68  fof(f77,plain,(
% 2.19/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.19/0.68    inference(cnf_transformation,[],[f32])).
% 2.19/0.68  fof(f32,plain,(
% 2.19/0.68    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.68    inference(ennf_transformation,[],[f24])).
% 2.19/0.68  fof(f24,axiom,(
% 2.19/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.19/0.68  fof(f100,plain,(
% 2.19/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.68    inference(cnf_transformation,[],[f47])).
% 2.19/0.68  fof(f47,plain,(
% 2.19/0.68    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.68    inference(flattening,[],[f46])).
% 2.19/0.68  fof(f46,plain,(
% 2.19/0.68    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.19/0.68    inference(ennf_transformation,[],[f15])).
% 2.19/0.68  fof(f15,axiom,(
% 2.19/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.19/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.19/0.68  fof(f175,plain,(
% 2.19/0.68    ~spl5_3 | spl5_4),
% 2.19/0.68    inference(avatar_split_clause,[],[f168,f173,f170])).
% 2.19/0.69  fof(f168,plain,(
% 2.19/0.69    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.69    inference(global_subsumption,[],[f70,f167])).
% 2.19/0.69  fof(f167,plain,(
% 2.19/0.69    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.19/0.69    inference(superposition,[],[f91,f164])).
% 2.19/0.69  fof(f164,plain,(
% 2.19/0.69    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.19/0.69    inference(global_subsumption,[],[f70,f156])).
% 2.19/0.69  fof(f156,plain,(
% 2.19/0.69    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 2.19/0.69    inference(resolution,[],[f71,f76])).
% 2.19/0.69  fof(f76,plain,(
% 2.19/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f31])).
% 2.19/0.69  fof(f31,plain,(
% 2.19/0.69    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.69    inference(ennf_transformation,[],[f23])).
% 2.19/0.69  fof(f23,axiom,(
% 2.19/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 2.19/0.69  fof(f91,plain,(
% 2.19/0.69    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f43])).
% 2.19/0.69  fof(f43,plain,(
% 2.19/0.69    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.19/0.69    inference(flattening,[],[f42])).
% 2.19/0.69  fof(f42,plain,(
% 2.19/0.69    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.19/0.69    inference(ennf_transformation,[],[f19])).
% 2.19/0.69  fof(f19,axiom,(
% 2.19/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.19/0.69  fof(f151,plain,(
% 2.19/0.69    spl5_1 | spl5_2),
% 2.19/0.69    inference(avatar_split_clause,[],[f72,f146,f143])).
% 2.19/0.69  fof(f72,plain,(
% 2.19/0.69    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.19/0.69    inference(cnf_transformation,[],[f52])).
% 2.19/0.69  fof(f148,plain,(
% 2.19/0.69    ~spl5_1 | ~spl5_2),
% 2.19/0.69    inference(avatar_split_clause,[],[f73,f146,f143])).
% 2.19/0.69  fof(f73,plain,(
% 2.19/0.69    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.19/0.69    inference(cnf_transformation,[],[f52])).
% 2.19/0.69  % SZS output end Proof for theBenchmark
% 2.19/0.69  % (27238)------------------------------
% 2.19/0.69  % (27238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.69  % (27238)Termination reason: Refutation
% 2.19/0.69  
% 2.19/0.69  % (27238)Memory used [KB]: 12281
% 2.19/0.69  % (27238)Time elapsed: 0.254 s
% 2.19/0.69  % (27238)------------------------------
% 2.19/0.69  % (27238)------------------------------
% 2.19/0.69  % (27235)Success in time 0.33 s
%------------------------------------------------------------------------------
