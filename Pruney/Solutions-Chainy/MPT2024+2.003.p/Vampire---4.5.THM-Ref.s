%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:09 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 416 expanded)
%              Number of leaves         :   45 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  815 (1693 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f130,f158,f200,f201,f238,f247,f290,f303,f327,f344,f348,f402,f497,f501,f540,f1177])).

fof(f1177,plain,
    ( ~ spl5_22
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f1176])).

fof(f1176,plain,
    ( $false
    | ~ spl5_22
    | spl5_33 ),
    inference(subsumption_resolution,[],[f1171,f289])).

fof(f289,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl5_22
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1171,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_33 ),
    inference(resolution,[],[f714,f496])).

fof(f496,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl5_33
  <=> r2_hidden(sK1,k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f714,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f355,f390])).

fof(f390,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f210,f85])).

fof(f85,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(subsumption_resolution,[],[f209,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X2)
      | r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(superposition,[],[f69,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f355,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k1_tarski(X3),k2_xboole_0(X4,X5))
      | ~ r2_hidden(X3,X4) ) ),
    inference(superposition,[],[f168,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f168,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f70,f73])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f540,plain,
    ( ~ spl5_24
    | ~ spl5_26
    | spl5_32 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | ~ spl5_24
    | ~ spl5_26
    | spl5_32 ),
    inference(subsumption_resolution,[],[f538,f338])).

fof(f338,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl5_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f538,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_24
    | spl5_32 ),
    inference(subsumption_resolution,[],[f533,f321])).

fof(f321,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl5_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f533,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_32 ),
    inference(resolution,[],[f492,f218])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f86,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f492,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f490])).

fof(f490,plain,
    ( spl5_32
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f501,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_25
    | ~ spl5_26
    | ~ spl5_27
    | spl5_31 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_25
    | ~ spl5_26
    | ~ spl5_27
    | spl5_31 ),
    inference(unit_resulting_resolution,[],[f124,f119,f343,f326,f338,f321,f488,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f488,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl5_31
  <=> v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f326,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl5_25
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f343,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl5_27
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f119,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f124,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f497,plain,
    ( ~ spl5_31
    | ~ spl5_32
    | ~ spl5_33
    | spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f484,f127,f122,f117,f97,f494,f490,f486])).

fof(f97,plain,
    ( spl5_1
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f127,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f484,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f483,f129])).

fof(f129,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f483,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | spl5_1
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f482,f124])).

fof(f482,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f477,f119])).

fof(f477,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | spl5_1 ),
    inference(resolution,[],[f293,f99])).

fof(f99,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f293,plain,(
    ! [X6,X8,X7] :
      ( m1_subset_1(X6,u1_struct_0(k9_yellow_6(X7,X8)))
      | ~ r2_hidden(X8,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ v3_pre_topc(X6,X7) ) ),
    inference(resolution,[],[f280,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f280,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f77,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f402,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_19
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_19
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f246,f339,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f339,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f337])).

fof(f246,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl5_19
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f114,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f348,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_18
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_18
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f237,f322,f79])).

fof(f322,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f320])).

fof(f237,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl5_18
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f344,plain,
    ( ~ spl5_26
    | spl5_27
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f335,f196,f127,f122,f117,f112,f341,f337])).

fof(f196,plain,
    ( spl5_17
  <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f335,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f334,f129])).

fof(f334,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f333,f124])).

fof(f333,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f332,f119])).

fof(f332,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f328,f114])).

fof(f328,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_17 ),
    inference(resolution,[],[f198,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f198,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f196])).

fof(f327,plain,
    ( ~ spl5_24
    | spl5_25
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f318,f190,f127,f122,f117,f112,f324,f320])).

fof(f190,plain,
    ( spl5_16
  <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f318,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f317,f129])).

fof(f317,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f316,f124])).

fof(f316,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f315,f119])).

fof(f315,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f311,f114])).

fof(f311,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f192,f76])).

fof(f192,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f303,plain,
    ( ~ spl5_12
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f299,f287,f155])).

fof(f155,plain,
    ( spl5_12
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f299,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_22 ),
    inference(resolution,[],[f289,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f290,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f285,f244,f127,f122,f117,f112,f287])).

fof(f285,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f284,f129])).

fof(f284,plain,
    ( r2_hidden(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f283,f124])).

fof(f283,plain,
    ( r2_hidden(sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f282,f119])).

fof(f282,plain,
    ( r2_hidden(sK1,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f281,f114])).

fof(f281,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_19 ),
    inference(resolution,[],[f246,f248])).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f81,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f247,plain,
    ( spl5_19
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f242,f127,f122,f117,f112,f107,f244])).

fof(f107,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f242,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f241,f129])).

fof(f241,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f240,f124])).

fof(f240,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f239,f119])).

fof(f239,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f227,f114])).

fof(f227,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f74,f109])).

fof(f109,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f238,plain,
    ( spl5_18
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f233,f127,f122,f117,f112,f102,f235])).

fof(f102,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f233,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f232,f129])).

fof(f232,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f231,f124])).

fof(f231,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f230,f119])).

fof(f230,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f226,f114])).

fof(f226,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f74,f104])).

fof(f104,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f201,plain,
    ( spl5_10
    | spl5_16
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f179,f102,f190,f146])).

fof(f146,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f179,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f87,f104])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f200,plain,
    ( spl5_10
    | spl5_17
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f180,f107,f196,f146])).

fof(f180,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_3 ),
    inference(resolution,[],[f87,f109])).

fof(f158,plain,
    ( ~ spl5_10
    | spl5_12
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f135,f107,f155,f146])).

fof(f135,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_3 ),
    inference(resolution,[],[f89,f109])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f130,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f60,f127])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f49,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
      & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f125,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f61,f122])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f120,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f62,f117])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f115,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f63,f112])).

fof(f63,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f110,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f64,f107])).

fof(f64,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f65,f102])).

fof(f65,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f66,f97])).

fof(f66,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:03:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (10567)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (10580)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (10595)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (10567)Refutation not found, incomplete strategy% (10567)------------------------------
% 0.22/0.52  % (10567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10567)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10567)Memory used [KB]: 1663
% 0.22/0.52  % (10567)Time elapsed: 0.107 s
% 0.22/0.52  % (10567)------------------------------
% 0.22/0.52  % (10567)------------------------------
% 0.22/0.52  % (10568)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (10584)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (10570)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (10595)Refutation not found, incomplete strategy% (10595)------------------------------
% 0.22/0.52  % (10595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10587)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (10579)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (10595)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10595)Memory used [KB]: 1663
% 0.22/0.53  % (10595)Time elapsed: 0.110 s
% 0.22/0.53  % (10595)------------------------------
% 0.22/0.53  % (10595)------------------------------
% 0.22/0.53  % (10571)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (10576)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (10572)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (10569)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (10566)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (10577)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.54  % (10592)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (10585)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.54  % (10589)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.54  % (10586)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.54  % (10592)Refutation not found, incomplete strategy% (10592)------------------------------
% 1.33/0.54  % (10592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (10592)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (10592)Memory used [KB]: 6268
% 1.33/0.54  % (10592)Time elapsed: 0.131 s
% 1.33/0.54  % (10592)------------------------------
% 1.33/0.54  % (10592)------------------------------
% 1.33/0.55  % (10573)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.55  % (10593)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.55  % (10591)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.55  % (10578)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.55  % (10583)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.55  % (10578)Refutation not found, incomplete strategy% (10578)------------------------------
% 1.33/0.55  % (10578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (10578)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (10578)Memory used [KB]: 10618
% 1.33/0.55  % (10578)Time elapsed: 0.138 s
% 1.33/0.55  % (10578)------------------------------
% 1.33/0.55  % (10578)------------------------------
% 1.33/0.55  % (10588)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.33/0.55  % (10581)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.56  % (10575)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.56  % (10574)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.56  % (10576)Refutation not found, incomplete strategy% (10576)------------------------------
% 1.33/0.56  % (10576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (10576)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (10576)Memory used [KB]: 10874
% 1.33/0.56  % (10576)Time elapsed: 0.124 s
% 1.33/0.56  % (10576)------------------------------
% 1.33/0.56  % (10576)------------------------------
% 1.47/0.56  % (10594)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.47/0.56  % (10594)Refutation not found, incomplete strategy% (10594)------------------------------
% 1.47/0.56  % (10594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (10590)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.57  % (10582)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.47/0.57  % (10582)Refutation not found, incomplete strategy% (10582)------------------------------
% 1.47/0.57  % (10582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (10582)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (10582)Memory used [KB]: 10746
% 1.47/0.57  % (10582)Time elapsed: 0.139 s
% 1.47/0.57  % (10582)------------------------------
% 1.47/0.57  % (10582)------------------------------
% 1.47/0.58  % (10594)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (10594)Memory used [KB]: 10874
% 1.47/0.58  % (10594)Time elapsed: 0.124 s
% 1.47/0.58  % (10594)------------------------------
% 1.47/0.58  % (10594)------------------------------
% 1.47/0.60  % (10587)Refutation found. Thanks to Tanya!
% 1.47/0.60  % SZS status Theorem for theBenchmark
% 1.47/0.62  % SZS output start Proof for theBenchmark
% 1.47/0.62  fof(f1178,plain,(
% 1.47/0.62    $false),
% 1.47/0.62    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f130,f158,f200,f201,f238,f247,f290,f303,f327,f344,f348,f402,f497,f501,f540,f1177])).
% 1.47/0.62  fof(f1177,plain,(
% 1.47/0.62    ~spl5_22 | spl5_33),
% 1.47/0.62    inference(avatar_contradiction_clause,[],[f1176])).
% 1.47/0.62  fof(f1176,plain,(
% 1.47/0.62    $false | (~spl5_22 | spl5_33)),
% 1.47/0.62    inference(subsumption_resolution,[],[f1171,f289])).
% 1.47/0.62  fof(f289,plain,(
% 1.47/0.62    r2_hidden(sK1,sK2) | ~spl5_22),
% 1.47/0.62    inference(avatar_component_clause,[],[f287])).
% 1.47/0.62  fof(f287,plain,(
% 1.47/0.62    spl5_22 <=> r2_hidden(sK1,sK2)),
% 1.47/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.47/0.62  fof(f1171,plain,(
% 1.47/0.62    ~r2_hidden(sK1,sK2) | spl5_33),
% 1.47/0.62    inference(resolution,[],[f714,f496])).
% 1.47/0.62  fof(f496,plain,(
% 1.47/0.62    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | spl5_33),
% 1.47/0.62    inference(avatar_component_clause,[],[f494])).
% 1.47/0.62  fof(f494,plain,(
% 1.47/0.62    spl5_33 <=> r2_hidden(sK1,k2_xboole_0(sK2,sK3))),
% 1.47/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.47/0.62  fof(f714,plain,(
% 1.47/0.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,X2)) | ~r2_hidden(X0,X1)) )),
% 1.47/0.62    inference(resolution,[],[f355,f390])).
% 1.47/0.62  fof(f390,plain,(
% 1.47/0.62    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.47/0.62    inference(superposition,[],[f210,f85])).
% 1.47/0.62  fof(f85,plain,(
% 1.47/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.47/0.62    inference(cnf_transformation,[],[f6])).
% 1.47/0.62  fof(f6,axiom,(
% 1.47/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.62  fof(f210,plain,(
% 1.47/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.47/0.62    inference(subsumption_resolution,[],[f209,f94])).
% 1.47/0.62  fof(f94,plain,(
% 1.47/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.47/0.62    inference(equality_resolution,[],[f83])).
% 1.47/0.62  fof(f83,plain,(
% 1.47/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.47/0.62    inference(cnf_transformation,[],[f54])).
% 1.47/0.62  fof(f54,plain,(
% 1.47/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.62    inference(flattening,[],[f53])).
% 1.47/0.62  fof(f53,plain,(
% 1.47/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.62    inference(nnf_transformation,[],[f2])).
% 1.47/0.62  fof(f2,axiom,(
% 1.47/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.62  fof(f209,plain,(
% 1.47/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,X2) | r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.47/0.62    inference(superposition,[],[f69,f72])).
% 1.47/0.62  fof(f72,plain,(
% 1.47/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.47/0.62    inference(cnf_transformation,[],[f31])).
% 1.47/0.62  fof(f31,plain,(
% 1.47/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.47/0.62    inference(ennf_transformation,[],[f4])).
% 1.47/0.62  fof(f4,axiom,(
% 1.47/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.47/0.62  fof(f69,plain,(
% 1.47/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) | r2_hidden(X0,X2)) )),
% 1.47/0.62    inference(cnf_transformation,[],[f28])).
% 1.47/0.62  fof(f28,plain,(
% 1.47/0.62    ! [X0,X1,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 1.47/0.62    inference(ennf_transformation,[],[f9])).
% 1.47/0.62  fof(f9,axiom,(
% 1.47/0.62    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 1.47/0.63  fof(f355,plain,(
% 1.47/0.63    ( ! [X4,X5,X3] : (r1_tarski(k1_tarski(X3),k2_xboole_0(X4,X5)) | ~r2_hidden(X3,X4)) )),
% 1.47/0.63    inference(superposition,[],[f168,f71])).
% 1.47/0.63  fof(f71,plain,(
% 1.47/0.63    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f30])).
% 1.47/0.63  fof(f30,plain,(
% 1.47/0.63    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.47/0.63    inference(ennf_transformation,[],[f7])).
% 1.47/0.63  fof(f7,axiom,(
% 1.47/0.63    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.47/0.63  fof(f168,plain,(
% 1.47/0.63    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 1.47/0.63    inference(resolution,[],[f70,f73])).
% 1.47/0.63  fof(f73,plain,(
% 1.47/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.47/0.63    inference(cnf_transformation,[],[f5])).
% 1.47/0.63  fof(f5,axiom,(
% 1.47/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.47/0.63  fof(f70,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f29])).
% 1.47/0.63  fof(f29,plain,(
% 1.47/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.47/0.63    inference(ennf_transformation,[],[f3])).
% 1.47/0.63  fof(f3,axiom,(
% 1.47/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.47/0.63  fof(f540,plain,(
% 1.47/0.63    ~spl5_24 | ~spl5_26 | spl5_32),
% 1.47/0.63    inference(avatar_contradiction_clause,[],[f539])).
% 1.47/0.63  fof(f539,plain,(
% 1.47/0.63    $false | (~spl5_24 | ~spl5_26 | spl5_32)),
% 1.47/0.63    inference(subsumption_resolution,[],[f538,f338])).
% 1.47/0.63  fof(f338,plain,(
% 1.47/0.63    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_26),
% 1.47/0.63    inference(avatar_component_clause,[],[f337])).
% 1.47/0.63  fof(f337,plain,(
% 1.47/0.63    spl5_26 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.47/0.63  fof(f538,plain,(
% 1.47/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_24 | spl5_32)),
% 1.47/0.63    inference(subsumption_resolution,[],[f533,f321])).
% 1.47/0.63  fof(f321,plain,(
% 1.47/0.63    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_24),
% 1.47/0.63    inference(avatar_component_clause,[],[f320])).
% 1.47/0.63  fof(f320,plain,(
% 1.47/0.63    spl5_24 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.47/0.63  fof(f533,plain,(
% 1.47/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_32),
% 1.47/0.63    inference(resolution,[],[f492,f218])).
% 1.47/0.63  fof(f218,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.47/0.63    inference(duplicate_literal_removal,[],[f217])).
% 1.47/0.63  fof(f217,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.47/0.63    inference(superposition,[],[f86,f67])).
% 1.47/0.63  fof(f67,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.47/0.63    inference(cnf_transformation,[],[f25])).
% 1.47/0.63  fof(f25,plain,(
% 1.47/0.63    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.63    inference(flattening,[],[f24])).
% 1.47/0.63  fof(f24,plain,(
% 1.47/0.63    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.47/0.63    inference(ennf_transformation,[],[f12])).
% 1.47/0.63  fof(f12,axiom,(
% 1.47/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.47/0.63  fof(f86,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.47/0.63    inference(cnf_transformation,[],[f44])).
% 1.47/0.63  fof(f44,plain,(
% 1.47/0.63    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.63    inference(flattening,[],[f43])).
% 1.47/0.63  fof(f43,plain,(
% 1.47/0.63    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.47/0.63    inference(ennf_transformation,[],[f11])).
% 1.47/0.63  fof(f11,axiom,(
% 1.47/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.47/0.63  fof(f492,plain,(
% 1.47/0.63    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_32),
% 1.47/0.63    inference(avatar_component_clause,[],[f490])).
% 1.47/0.63  fof(f490,plain,(
% 1.47/0.63    spl5_32 <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.47/0.63  fof(f501,plain,(
% 1.47/0.63    ~spl5_5 | ~spl5_6 | ~spl5_24 | ~spl5_25 | ~spl5_26 | ~spl5_27 | spl5_31),
% 1.47/0.63    inference(avatar_contradiction_clause,[],[f499])).
% 1.47/0.63  fof(f499,plain,(
% 1.47/0.63    $false | (~spl5_5 | ~spl5_6 | ~spl5_24 | ~spl5_25 | ~spl5_26 | ~spl5_27 | spl5_31)),
% 1.47/0.63    inference(unit_resulting_resolution,[],[f124,f119,f343,f326,f338,f321,f488,f68])).
% 1.47/0.63  fof(f68,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f27])).
% 1.47/0.63  fof(f27,plain,(
% 1.47/0.63    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.47/0.63    inference(flattening,[],[f26])).
% 1.47/0.63  fof(f26,plain,(
% 1.47/0.63    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.47/0.63    inference(ennf_transformation,[],[f15])).
% 1.47/0.63  fof(f15,axiom,(
% 1.47/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).
% 1.47/0.63  fof(f488,plain,(
% 1.47/0.63    ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | spl5_31),
% 1.47/0.63    inference(avatar_component_clause,[],[f486])).
% 1.47/0.63  fof(f486,plain,(
% 1.47/0.63    spl5_31 <=> v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.47/0.63  fof(f326,plain,(
% 1.47/0.63    v3_pre_topc(sK3,sK0) | ~spl5_25),
% 1.47/0.63    inference(avatar_component_clause,[],[f324])).
% 1.47/0.63  fof(f324,plain,(
% 1.47/0.63    spl5_25 <=> v3_pre_topc(sK3,sK0)),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.47/0.63  fof(f343,plain,(
% 1.47/0.63    v3_pre_topc(sK2,sK0) | ~spl5_27),
% 1.47/0.63    inference(avatar_component_clause,[],[f341])).
% 1.47/0.63  fof(f341,plain,(
% 1.47/0.63    spl5_27 <=> v3_pre_topc(sK2,sK0)),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.47/0.63  fof(f119,plain,(
% 1.47/0.63    l1_pre_topc(sK0) | ~spl5_5),
% 1.47/0.63    inference(avatar_component_clause,[],[f117])).
% 1.47/0.63  fof(f117,plain,(
% 1.47/0.63    spl5_5 <=> l1_pre_topc(sK0)),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.47/0.63  fof(f124,plain,(
% 1.47/0.63    v2_pre_topc(sK0) | ~spl5_6),
% 1.47/0.63    inference(avatar_component_clause,[],[f122])).
% 1.47/0.63  fof(f122,plain,(
% 1.47/0.63    spl5_6 <=> v2_pre_topc(sK0)),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.47/0.63  fof(f497,plain,(
% 1.47/0.63    ~spl5_31 | ~spl5_32 | ~spl5_33 | spl5_1 | ~spl5_5 | ~spl5_6 | spl5_7),
% 1.47/0.63    inference(avatar_split_clause,[],[f484,f127,f122,f117,f97,f494,f490,f486])).
% 1.47/0.63  fof(f97,plain,(
% 1.47/0.63    spl5_1 <=> m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.47/0.63  fof(f127,plain,(
% 1.47/0.63    spl5_7 <=> v2_struct_0(sK0)),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.47/0.63  fof(f484,plain,(
% 1.47/0.63    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | (spl5_1 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 1.47/0.63    inference(subsumption_resolution,[],[f483,f129])).
% 1.47/0.63  fof(f129,plain,(
% 1.47/0.63    ~v2_struct_0(sK0) | spl5_7),
% 1.47/0.63    inference(avatar_component_clause,[],[f127])).
% 1.47/0.63  fof(f483,plain,(
% 1.47/0.63    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | (spl5_1 | ~spl5_5 | ~spl5_6)),
% 1.47/0.63    inference(subsumption_resolution,[],[f482,f124])).
% 1.47/0.63  fof(f482,plain,(
% 1.47/0.63    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | (spl5_1 | ~spl5_5)),
% 1.47/0.63    inference(subsumption_resolution,[],[f477,f119])).
% 1.47/0.63  fof(f477,plain,(
% 1.47/0.63    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | spl5_1),
% 1.47/0.63    inference(resolution,[],[f293,f99])).
% 1.47/0.63  fof(f99,plain,(
% 1.47/0.63    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl5_1),
% 1.47/0.63    inference(avatar_component_clause,[],[f97])).
% 1.47/0.63  fof(f293,plain,(
% 1.47/0.63    ( ! [X6,X8,X7] : (m1_subset_1(X6,u1_struct_0(k9_yellow_6(X7,X8))) | ~r2_hidden(X8,X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7))) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~v3_pre_topc(X6,X7)) )),
% 1.47/0.63    inference(resolution,[],[f280,f80])).
% 1.47/0.63  fof(f80,plain,(
% 1.47/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f40])).
% 1.47/0.63  fof(f40,plain,(
% 1.47/0.63    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.47/0.63    inference(ennf_transformation,[],[f13])).
% 1.47/0.63  fof(f13,axiom,(
% 1.47/0.63    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.47/0.63  fof(f280,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.63    inference(subsumption_resolution,[],[f77,f78])).
% 1.47/0.63  fof(f78,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f37])).
% 1.47/0.63  fof(f37,plain,(
% 1.47/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.47/0.63    inference(flattening,[],[f36])).
% 1.47/0.63  fof(f36,plain,(
% 1.47/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.47/0.63    inference(ennf_transformation,[],[f14])).
% 1.47/0.63  fof(f14,axiom,(
% 1.47/0.63    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.47/0.63  fof(f77,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f52])).
% 1.47/0.63  fof(f52,plain,(
% 1.47/0.63    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.63    inference(flattening,[],[f51])).
% 1.47/0.63  fof(f51,plain,(
% 1.47/0.63    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.63    inference(nnf_transformation,[],[f35])).
% 1.47/0.63  fof(f35,plain,(
% 1.47/0.63    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.63    inference(flattening,[],[f34])).
% 1.47/0.63  fof(f34,plain,(
% 1.47/0.63    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.63    inference(ennf_transformation,[],[f18])).
% 1.47/0.63  fof(f18,axiom,(
% 1.47/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 1.47/0.63  fof(f402,plain,(
% 1.47/0.63    ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_19 | spl5_26),
% 1.47/0.63    inference(avatar_contradiction_clause,[],[f399])).
% 1.47/0.63  fof(f399,plain,(
% 1.47/0.63    $false | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_19 | spl5_26)),
% 1.47/0.63    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f246,f339,f79])).
% 1.47/0.63  fof(f79,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f39])).
% 1.47/0.63  fof(f39,plain,(
% 1.47/0.63    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.63    inference(flattening,[],[f38])).
% 1.47/0.63  fof(f38,plain,(
% 1.47/0.63    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.63    inference(ennf_transformation,[],[f16])).
% 1.47/0.63  fof(f16,axiom,(
% 1.47/0.63    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.47/0.63  fof(f339,plain,(
% 1.47/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_26),
% 1.47/0.63    inference(avatar_component_clause,[],[f337])).
% 1.47/0.63  fof(f246,plain,(
% 1.47/0.63    m1_connsp_2(sK2,sK0,sK1) | ~spl5_19),
% 1.47/0.63    inference(avatar_component_clause,[],[f244])).
% 1.47/0.63  fof(f244,plain,(
% 1.47/0.63    spl5_19 <=> m1_connsp_2(sK2,sK0,sK1)),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.47/0.63  fof(f114,plain,(
% 1.47/0.63    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 1.47/0.63    inference(avatar_component_clause,[],[f112])).
% 1.47/0.63  fof(f112,plain,(
% 1.47/0.63    spl5_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.47/0.63  fof(f348,plain,(
% 1.47/0.63    ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_18 | spl5_24),
% 1.47/0.63    inference(avatar_contradiction_clause,[],[f345])).
% 1.47/0.63  fof(f345,plain,(
% 1.47/0.63    $false | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_18 | spl5_24)),
% 1.47/0.63    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f237,f322,f79])).
% 1.47/0.63  fof(f322,plain,(
% 1.47/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_24),
% 1.47/0.63    inference(avatar_component_clause,[],[f320])).
% 1.47/0.63  fof(f237,plain,(
% 1.47/0.63    m1_connsp_2(sK3,sK0,sK1) | ~spl5_18),
% 1.47/0.63    inference(avatar_component_clause,[],[f235])).
% 1.47/0.63  fof(f235,plain,(
% 1.47/0.63    spl5_18 <=> m1_connsp_2(sK3,sK0,sK1)),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.47/0.63  fof(f344,plain,(
% 1.47/0.63    ~spl5_26 | spl5_27 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_17),
% 1.47/0.63    inference(avatar_split_clause,[],[f335,f196,f127,f122,f117,f112,f341,f337])).
% 1.47/0.63  fof(f196,plain,(
% 1.47/0.63    spl5_17 <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.47/0.63  fof(f335,plain,(
% 1.47/0.63    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_17)),
% 1.47/0.63    inference(subsumption_resolution,[],[f334,f129])).
% 1.47/0.63  fof(f334,plain,(
% 1.47/0.63    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_17)),
% 1.47/0.63    inference(subsumption_resolution,[],[f333,f124])).
% 1.47/0.63  fof(f333,plain,(
% 1.47/0.63    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_17)),
% 1.47/0.63    inference(subsumption_resolution,[],[f332,f119])).
% 1.47/0.63  fof(f332,plain,(
% 1.47/0.63    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_17)),
% 1.47/0.63    inference(subsumption_resolution,[],[f328,f114])).
% 1.47/0.63  fof(f328,plain,(
% 1.47/0.63    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_17),
% 1.47/0.63    inference(resolution,[],[f198,f76])).
% 1.47/0.63  fof(f76,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f52])).
% 1.47/0.63  fof(f198,plain,(
% 1.47/0.63    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_17),
% 1.47/0.63    inference(avatar_component_clause,[],[f196])).
% 1.47/0.63  fof(f327,plain,(
% 1.47/0.63    ~spl5_24 | spl5_25 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16),
% 1.47/0.63    inference(avatar_split_clause,[],[f318,f190,f127,f122,f117,f112,f324,f320])).
% 1.47/0.63  fof(f190,plain,(
% 1.47/0.63    spl5_16 <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.47/0.63  fof(f318,plain,(
% 1.47/0.63    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16)),
% 1.47/0.63    inference(subsumption_resolution,[],[f317,f129])).
% 1.47/0.63  fof(f317,plain,(
% 1.47/0.63    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_16)),
% 1.47/0.63    inference(subsumption_resolution,[],[f316,f124])).
% 1.47/0.63  fof(f316,plain,(
% 1.47/0.63    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_16)),
% 1.47/0.63    inference(subsumption_resolution,[],[f315,f119])).
% 1.47/0.63  fof(f315,plain,(
% 1.47/0.63    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_16)),
% 1.47/0.63    inference(subsumption_resolution,[],[f311,f114])).
% 1.47/0.63  fof(f311,plain,(
% 1.47/0.63    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_16),
% 1.47/0.63    inference(resolution,[],[f192,f76])).
% 1.47/0.63  fof(f192,plain,(
% 1.47/0.63    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_16),
% 1.47/0.63    inference(avatar_component_clause,[],[f190])).
% 1.47/0.63  fof(f303,plain,(
% 1.47/0.63    ~spl5_12 | ~spl5_22),
% 1.47/0.63    inference(avatar_split_clause,[],[f299,f287,f155])).
% 1.47/0.63  fof(f155,plain,(
% 1.47/0.63    spl5_12 <=> v1_xboole_0(sK2)),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.47/0.63  fof(f299,plain,(
% 1.47/0.63    ~v1_xboole_0(sK2) | ~spl5_22),
% 1.47/0.63    inference(resolution,[],[f289,f91])).
% 1.47/0.63  fof(f91,plain,(
% 1.47/0.63    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f59])).
% 1.47/0.63  fof(f59,plain,(
% 1.47/0.63    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).
% 1.47/0.63  fof(f58,plain,(
% 1.47/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.47/0.63    introduced(choice_axiom,[])).
% 1.47/0.63  fof(f57,plain,(
% 1.47/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.63    inference(rectify,[],[f56])).
% 1.47/0.63  fof(f56,plain,(
% 1.47/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.63    inference(nnf_transformation,[],[f1])).
% 1.47/0.63  fof(f1,axiom,(
% 1.47/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.47/0.63  fof(f290,plain,(
% 1.47/0.63    spl5_22 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_19),
% 1.47/0.63    inference(avatar_split_clause,[],[f285,f244,f127,f122,f117,f112,f287])).
% 1.47/0.63  fof(f285,plain,(
% 1.47/0.63    r2_hidden(sK1,sK2) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_19)),
% 1.47/0.63    inference(subsumption_resolution,[],[f284,f129])).
% 1.47/0.63  fof(f284,plain,(
% 1.47/0.63    r2_hidden(sK1,sK2) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_19)),
% 1.47/0.63    inference(subsumption_resolution,[],[f283,f124])).
% 1.47/0.63  fof(f283,plain,(
% 1.47/0.63    r2_hidden(sK1,sK2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_19)),
% 1.47/0.63    inference(subsumption_resolution,[],[f282,f119])).
% 1.47/0.63  fof(f282,plain,(
% 1.47/0.63    r2_hidden(sK1,sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_19)),
% 1.47/0.63    inference(subsumption_resolution,[],[f281,f114])).
% 1.47/0.63  fof(f281,plain,(
% 1.47/0.63    r2_hidden(sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_19),
% 1.47/0.63    inference(resolution,[],[f246,f248])).
% 1.47/0.63  fof(f248,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.63    inference(subsumption_resolution,[],[f81,f79])).
% 1.47/0.63  fof(f81,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f42])).
% 1.47/0.63  fof(f42,plain,(
% 1.47/0.63    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.63    inference(flattening,[],[f41])).
% 1.47/0.63  fof(f41,plain,(
% 1.47/0.63    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.63    inference(ennf_transformation,[],[f17])).
% 1.47/0.63  fof(f17,axiom,(
% 1.47/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 1.47/0.63  fof(f247,plain,(
% 1.47/0.63    spl5_19 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7),
% 1.47/0.63    inference(avatar_split_clause,[],[f242,f127,f122,f117,f112,f107,f244])).
% 1.47/0.63  fof(f107,plain,(
% 1.47/0.63    spl5_3 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.47/0.63  fof(f242,plain,(
% 1.47/0.63    m1_connsp_2(sK2,sK0,sK1) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 1.47/0.63    inference(subsumption_resolution,[],[f241,f129])).
% 1.47/0.63  fof(f241,plain,(
% 1.47/0.63    m1_connsp_2(sK2,sK0,sK1) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 1.47/0.63    inference(subsumption_resolution,[],[f240,f124])).
% 1.47/0.63  fof(f240,plain,(
% 1.47/0.63    m1_connsp_2(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.47/0.63    inference(subsumption_resolution,[],[f239,f119])).
% 1.47/0.63  fof(f239,plain,(
% 1.47/0.63    m1_connsp_2(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4)),
% 1.47/0.63    inference(subsumption_resolution,[],[f227,f114])).
% 1.47/0.63  fof(f227,plain,(
% 1.47/0.63    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 1.47/0.63    inference(resolution,[],[f74,f109])).
% 1.47/0.63  fof(f109,plain,(
% 1.47/0.63    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_3),
% 1.47/0.63    inference(avatar_component_clause,[],[f107])).
% 1.47/0.63  fof(f74,plain,(
% 1.47/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f33])).
% 1.47/0.63  fof(f33,plain,(
% 1.47/0.63    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.63    inference(flattening,[],[f32])).
% 1.47/0.63  fof(f32,plain,(
% 1.47/0.63    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.63    inference(ennf_transformation,[],[f19])).
% 1.47/0.63  fof(f19,axiom,(
% 1.47/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).
% 1.47/0.63  fof(f238,plain,(
% 1.47/0.63    spl5_18 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7),
% 1.47/0.63    inference(avatar_split_clause,[],[f233,f127,f122,f117,f112,f102,f235])).
% 1.47/0.63  fof(f102,plain,(
% 1.47/0.63    spl5_2 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.47/0.63  fof(f233,plain,(
% 1.47/0.63    m1_connsp_2(sK3,sK0,sK1) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 1.47/0.63    inference(subsumption_resolution,[],[f232,f129])).
% 1.47/0.63  fof(f232,plain,(
% 1.47/0.63    m1_connsp_2(sK3,sK0,sK1) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 1.47/0.63    inference(subsumption_resolution,[],[f231,f124])).
% 1.47/0.63  fof(f231,plain,(
% 1.47/0.63    m1_connsp_2(sK3,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 1.47/0.63    inference(subsumption_resolution,[],[f230,f119])).
% 1.47/0.63  fof(f230,plain,(
% 1.47/0.63    m1_connsp_2(sK3,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_4)),
% 1.47/0.63    inference(subsumption_resolution,[],[f226,f114])).
% 1.47/0.63  fof(f226,plain,(
% 1.47/0.63    m1_connsp_2(sK3,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 1.47/0.63    inference(resolution,[],[f74,f104])).
% 1.47/0.63  fof(f104,plain,(
% 1.47/0.63    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_2),
% 1.47/0.63    inference(avatar_component_clause,[],[f102])).
% 1.47/0.63  fof(f201,plain,(
% 1.47/0.63    spl5_10 | spl5_16 | ~spl5_2),
% 1.47/0.63    inference(avatar_split_clause,[],[f179,f102,f190,f146])).
% 1.47/0.63  fof(f146,plain,(
% 1.47/0.63    spl5_10 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.47/0.63  fof(f179,plain,(
% 1.47/0.63    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_2),
% 1.47/0.63    inference(resolution,[],[f87,f104])).
% 1.47/0.63  fof(f87,plain,(
% 1.47/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f55])).
% 1.47/0.63  fof(f55,plain,(
% 1.47/0.63    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.47/0.63    inference(nnf_transformation,[],[f45])).
% 1.47/0.63  fof(f45,plain,(
% 1.47/0.63    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.47/0.63    inference(ennf_transformation,[],[f10])).
% 1.47/0.63  fof(f10,axiom,(
% 1.47/0.63    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.47/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.47/0.63  fof(f200,plain,(
% 1.47/0.63    spl5_10 | spl5_17 | ~spl5_3),
% 1.47/0.63    inference(avatar_split_clause,[],[f180,f107,f196,f146])).
% 1.47/0.63  fof(f180,plain,(
% 1.47/0.63    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_3),
% 1.47/0.63    inference(resolution,[],[f87,f109])).
% 1.47/0.63  fof(f158,plain,(
% 1.47/0.63    ~spl5_10 | spl5_12 | ~spl5_3),
% 1.47/0.63    inference(avatar_split_clause,[],[f135,f107,f155,f146])).
% 1.47/0.63  fof(f135,plain,(
% 1.47/0.63    v1_xboole_0(sK2) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_3),
% 1.47/0.63    inference(resolution,[],[f89,f109])).
% 1.47/0.63  fof(f89,plain,(
% 1.47/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.47/0.63    inference(cnf_transformation,[],[f55])).
% 1.47/0.63  fof(f130,plain,(
% 1.47/0.63    ~spl5_7),
% 1.47/0.63    inference(avatar_split_clause,[],[f60,f127])).
% 1.47/0.63  fof(f60,plain,(
% 1.47/0.63    ~v2_struct_0(sK0)),
% 1.47/0.63    inference(cnf_transformation,[],[f50])).
% 1.47/0.63  fof(f50,plain,(
% 1.47/0.63    (((~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.47/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f49,f48,f47,f46])).
% 1.47/0.63  fof(f46,plain,(
% 1.47/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.47/0.63    introduced(choice_axiom,[])).
% 1.47/0.63  fof(f47,plain,(
% 1.47/0.63    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.47/0.63    introduced(choice_axiom,[])).
% 1.47/0.63  fof(f48,plain,(
% 1.47/0.63    ? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 1.47/0.63    introduced(choice_axiom,[])).
% 1.98/0.63  fof(f49,plain,(
% 1.98/0.63    ? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 1.98/0.63    introduced(choice_axiom,[])).
% 1.98/0.63  fof(f23,plain,(
% 1.98/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.98/0.63    inference(flattening,[],[f22])).
% 1.98/0.63  fof(f22,plain,(
% 1.98/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.98/0.63    inference(ennf_transformation,[],[f21])).
% 1.98/0.63  fof(f21,negated_conjecture,(
% 1.98/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.98/0.63    inference(negated_conjecture,[],[f20])).
% 1.98/0.63  fof(f20,conjecture,(
% 1.98/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).
% 1.98/0.63  fof(f125,plain,(
% 1.98/0.63    spl5_6),
% 1.98/0.63    inference(avatar_split_clause,[],[f61,f122])).
% 1.98/0.63  fof(f61,plain,(
% 1.98/0.63    v2_pre_topc(sK0)),
% 1.98/0.63    inference(cnf_transformation,[],[f50])).
% 1.98/0.63  fof(f120,plain,(
% 1.98/0.63    spl5_5),
% 1.98/0.63    inference(avatar_split_clause,[],[f62,f117])).
% 1.98/0.63  fof(f62,plain,(
% 1.98/0.63    l1_pre_topc(sK0)),
% 1.98/0.63    inference(cnf_transformation,[],[f50])).
% 1.98/0.63  fof(f115,plain,(
% 1.98/0.63    spl5_4),
% 1.98/0.63    inference(avatar_split_clause,[],[f63,f112])).
% 1.98/0.63  fof(f63,plain,(
% 1.98/0.63    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.98/0.63    inference(cnf_transformation,[],[f50])).
% 1.98/0.63  fof(f110,plain,(
% 1.98/0.63    spl5_3),
% 1.98/0.63    inference(avatar_split_clause,[],[f64,f107])).
% 1.98/0.63  fof(f64,plain,(
% 1.98/0.63    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.98/0.63    inference(cnf_transformation,[],[f50])).
% 1.98/0.63  fof(f105,plain,(
% 1.98/0.63    spl5_2),
% 1.98/0.63    inference(avatar_split_clause,[],[f65,f102])).
% 1.98/0.63  fof(f65,plain,(
% 1.98/0.63    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.98/0.63    inference(cnf_transformation,[],[f50])).
% 1.98/0.63  fof(f100,plain,(
% 1.98/0.63    ~spl5_1),
% 1.98/0.63    inference(avatar_split_clause,[],[f66,f97])).
% 1.98/0.63  fof(f66,plain,(
% 1.98/0.63    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.98/0.63    inference(cnf_transformation,[],[f50])).
% 1.98/0.63  % SZS output end Proof for theBenchmark
% 1.98/0.63  % (10587)------------------------------
% 1.98/0.63  % (10587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  % (10587)Termination reason: Refutation
% 1.98/0.64  
% 1.98/0.64  % (10587)Memory used [KB]: 7036
% 1.98/0.64  % (10587)Time elapsed: 0.201 s
% 1.98/0.64  % (10587)------------------------------
% 1.98/0.64  % (10587)------------------------------
% 1.98/0.64  % (10565)Success in time 0.263 s
%------------------------------------------------------------------------------
