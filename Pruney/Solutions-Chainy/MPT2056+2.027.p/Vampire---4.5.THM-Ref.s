%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 247 expanded)
%              Number of leaves         :   24 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  312 ( 787 expanded)
%              Number of equality atoms :   38 ( 153 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f261,f263,f265,f267,f269,f272,f380,f382,f384,f389,f396,f398])).

fof(f398,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f32,f362])).

fof(f362,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl4_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f14])).

% (12300)Termination reason: Refutation not found, incomplete strategy
fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

% (12300)Memory used [KB]: 1663
% (12300)Time elapsed: 0.110 s
% (12300)------------------------------
% (12300)------------------------------
fof(f396,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f31,f378])).

fof(f378,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl4_11
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f31,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f389,plain,
    ( ~ spl4_1
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | ~ spl4_1
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f34,f374,f282])).

fof(f282,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,k1_tarski(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | r1_xboole_0(sK1,k1_tarski(X0))
        | r1_xboole_0(sK1,k1_tarski(X0)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f273,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sK2(X0,k1_tarski(X1)) = X1
      | r1_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f273,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK2(sK1,X0))
        | r1_xboole_0(sK1,X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f240,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl4_1
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f374,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl4_10
  <=> r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f384,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f33,f370])).

fof(f370,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f382,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f54,f366])).

fof(f366,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f54,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))))) ),
    inference(definition_unfolding,[],[f30,f53,f37])).

fof(f37,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f53,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f52,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

fof(f35,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f17])).

fof(f380,plain,
    ( ~ spl4_10
    | spl4_7
    | ~ spl4_8
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_9
    | spl4_11 ),
    inference(avatar_split_clause,[],[f356,f376,f368,f258,f250,f246,f364,f360,f372])).

fof(f246,plain,
    ( spl4_3
  <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f250,plain,
    ( spl4_4
  <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f258,plain,
    ( spl4_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f356,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))))
    | v2_struct_0(sK0)
    | ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[],[f59,f302])).

fof(f302,plain,(
    ! [X0] :
      ( sK1 = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0)
      | ~ r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f172,f54])).

fof(f172,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(k3_lattice3(k1_lattice3(X6))))
      | k7_subset_1(X6,X4,X5) = X4
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f62,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f51,f53,f41])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f40,f37,f37,f53,f37,f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f272,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f32,f33,f244,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f244,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl4_2
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f269,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f26,f260])).

fof(f260,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f258])).

fof(f26,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f267,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f57,f256])).

fof(f256,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl4_5
  <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f57,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f27,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f265,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f56,f252])).

fof(f252,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f250])).

fof(f56,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f28,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f263,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f55,f248])).

fof(f248,plain,
    ( ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f246])).

fof(f55,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f29,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f261,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f237,f258,f254,f250,f246,f242,f239])).

fof(f237,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f58,f54])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | v1_xboole_0(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(definition_unfolding,[],[f38,f37,f37,f37,f53,f37])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (12300)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (12291)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (12282)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (12282)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (12300)Refutation not found, incomplete strategy% (12300)------------------------------
% 0.21/0.54  % (12300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f399,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f261,f263,f265,f267,f269,f272,f380,f382,f384,f389,f396,f398])).
% 0.21/0.54  fof(f398,plain,(
% 0.21/0.54    ~spl4_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f397])).
% 0.21/0.54  fof(f397,plain,(
% 0.21/0.54    $false | ~spl4_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f32,f362])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    v2_struct_0(sK0) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f360])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    spl4_7 <=> v2_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  % (12300)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.54  % (12300)Memory used [KB]: 1663
% 0.21/0.54  % (12300)Time elapsed: 0.110 s
% 0.21/0.54  % (12300)------------------------------
% 0.21/0.54  % (12300)------------------------------
% 0.21/0.54  fof(f396,plain,(
% 0.21/0.54    ~spl4_11),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f395])).
% 0.21/0.54  fof(f395,plain,(
% 0.21/0.54    $false | ~spl4_11),
% 0.21/0.54    inference(subsumption_resolution,[],[f31,f378])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl4_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f376])).
% 0.21/0.54  fof(f376,plain,(
% 0.21/0.54    spl4_11 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f389,plain,(
% 0.21/0.54    ~spl4_1 | spl4_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f385])).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    $false | (~spl4_1 | spl4_10)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f34,f374,f282])).
% 0.21/0.54  fof(f282,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(sK1,k1_tarski(X0)) | ~v1_xboole_0(X0)) ) | ~spl4_1),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f281])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | r1_xboole_0(sK1,k1_tarski(X0)) | r1_xboole_0(sK1,k1_tarski(X0))) ) | ~spl4_1),
% 0.21/0.54    inference(superposition,[],[f273,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK2(X0,k1_tarski(X1)) = X1 | r1_xboole_0(X0,k1_tarski(X1))) )),
% 0.21/0.54    inference(resolution,[],[f44,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(sK2(sK1,X0)) | r1_xboole_0(sK1,X0)) ) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f240,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) ) | ~spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f239])).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    spl4_1 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl4_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f372])).
% 0.21/0.54  fof(f372,plain,(
% 0.21/0.54    spl4_10 <=> r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f384,plain,(
% 0.21/0.54    spl4_9),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f383])).
% 0.21/0.54  fof(f383,plain,(
% 0.21/0.54    $false | spl4_9),
% 0.21/0.54    inference(subsumption_resolution,[],[f33,f370])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    ~l1_struct_0(sK0) | spl4_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f368])).
% 0.21/0.54  fof(f368,plain,(
% 0.21/0.54    spl4_9 <=> l1_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    l1_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f382,plain,(
% 0.21/0.54    spl4_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f381])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    $false | spl4_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f54,f366])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))))) | spl4_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f364])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    spl4_8 <=> m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))))),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f53,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f35,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f37])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f380,plain,(
% 0.21/0.54    ~spl4_10 | spl4_7 | ~spl4_8 | ~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_9 | spl4_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f356,f376,f368,f258,f250,f246,f364,f360,f372])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    spl4_3 <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    spl4_4 <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    spl4_6 <=> v1_xboole_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))))) | v2_struct_0(sK0) | ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.21/0.54    inference(superposition,[],[f59,f302])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    ( ! [X0] : (sK1 = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) | ~r1_xboole_0(sK1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f172,f54])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(k3_lattice3(k1_lattice3(X6)))) | k7_subset_1(X6,X4,X5) = X4 | ~r1_xboole_0(X4,X5)) )),
% 0.21/0.54    inference(superposition,[],[f62,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f46,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f51,f53,f41])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))))) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f40,f37,f37,f53,f37,f37])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 0.21/0.54  fof(f272,plain,(
% 0.21/0.54    ~spl4_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f270])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    $false | ~spl4_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f32,f33,f244,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    v1_xboole_0(k2_struct_0(sK0)) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f242])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    spl4_2 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    ~spl4_6),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f268])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    $false | ~spl4_6),
% 0.21/0.54    inference(subsumption_resolution,[],[f26,f260])).
% 0.21/0.54  fof(f260,plain,(
% 0.21/0.54    v1_xboole_0(sK1) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f258])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    spl4_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f266])).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    $false | spl4_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f57,f256])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f254])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    spl4_5 <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.54    inference(definition_unfolding,[],[f27,f37])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    spl4_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f264])).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    $false | spl4_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f56,f252])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f250])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.54    inference(definition_unfolding,[],[f28,f37])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f263,plain,(
% 0.21/0.54    spl4_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f262])).
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    $false | spl4_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f55,f248])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f246])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f37])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f237,f258,f254,f250,f246,f242,f239])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    ( ! [X0] : (v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(k2_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f58,f54])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f37,f37,f37,f53,f37])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (12282)------------------------------
% 0.21/0.54  % (12282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12282)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (12282)Memory used [KB]: 6396
% 0.21/0.54  % (12282)Time elapsed: 0.109 s
% 0.21/0.54  % (12282)------------------------------
% 0.21/0.54  % (12282)------------------------------
% 0.21/0.54  % (12271)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (12266)Success in time 0.173 s
%------------------------------------------------------------------------------
