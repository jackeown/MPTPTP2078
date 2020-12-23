%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 425 expanded)
%              Number of leaves         :   35 ( 166 expanded)
%              Depth                    :   16
%              Number of atoms          :  608 (1635 expanded)
%              Number of equality atoms :   46 ( 207 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f633,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f99,f106,f111,f122,f161,f175,f184,f197,f222,f259,f269,f385,f631])).

fof(f631,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_10
    | spl5_17
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_33 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_10
    | spl5_17
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f629,f221])).

fof(f221,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl5_17
  <=> k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f629,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_10
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_33 ),
    inference(forward_demodulation,[],[f628,f622])).

fof(f622,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_10
    | ~ spl5_20
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f618,f390])).

fof(f390,plain,
    ( m1_subset_1(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),u1_struct_0(sK0))
    | ~ spl5_4
    | ~ spl5_20
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f88,f258,f384,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ r2_hidden(X2,k2_pre_topc(X1,X0)) ) ),
    inference(resolution,[],[f66,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f384,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl5_33
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f258,plain,
    ( r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl5_20
  <=> r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f618,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))))
    | ~ m1_subset_1(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_10
    | ~ spl5_20 ),
    inference(resolution,[],[f294,f258])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_10 ),
    inference(forward_demodulation,[],[f293,f198])).

fof(f198,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_5
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f93,f120,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f65,f53])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f120,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f93,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_10 ),
    inference(forward_demodulation,[],[f291,f198])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f156,f93])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f155,f73])).

fof(f73,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f154,f78])).

fof(f78,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f153,f88])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f55,f83])).

fof(f83,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_3
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(f628,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_10
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f624,f390])).

fof(f624,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))))
    | ~ m1_subset_1(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_10
    | ~ spl5_22 ),
    inference(resolution,[],[f296,f268])).

fof(f268,plain,
    ( r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl5_22
  <=> r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f296,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_10 ),
    inference(forward_demodulation,[],[f295,f199])).

fof(f199,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl5_6
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f98,f120,f69])).

fof(f98,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f295,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_10 ),
    inference(forward_demodulation,[],[f292,f199])).

fof(f292,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f156,f98])).

fof(f385,plain,
    ( spl5_33
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f225,f115,f382])).

fof(f115,plain,
    ( spl5_9
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f225,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f117,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f53])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f117,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f269,plain,
    ( spl5_22
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_10 ),
    inference(avatar_split_clause,[],[f211,f119,f103,f96,f91,f266])).

fof(f103,plain,
    ( spl5_7
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f211,plain,
    ( r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_10 ),
    inference(backward_demodulation,[],[f204,f198])).

fof(f204,plain,
    ( r2_hidden(sK4(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_6
    | spl5_7
    | spl5_10 ),
    inference(backward_demodulation,[],[f112,f199])).

fof(f112,plain,
    ( r2_hidden(sK4(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f105,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f105,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f259,plain,
    ( spl5_20
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_10 ),
    inference(avatar_split_clause,[],[f210,f119,f103,f96,f91,f256])).

fof(f210,plain,
    ( r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_10 ),
    inference(backward_demodulation,[],[f205,f198])).

fof(f205,plain,
    ( r2_hidden(sK4(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl5_6
    | spl5_7
    | spl5_10 ),
    inference(backward_demodulation,[],[f113,f199])).

fof(f113,plain,
    ( r2_hidden(sK4(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f105,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f222,plain,
    ( ~ spl5_17
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | spl5_10 ),
    inference(avatar_split_clause,[],[f209,f119,f108,f96,f91,f219])).

fof(f108,plain,
    ( spl5_8
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f209,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK2,sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | spl5_10 ),
    inference(backward_demodulation,[],[f206,f198])).

fof(f206,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | ~ spl5_6
    | spl5_8
    | spl5_10 ),
    inference(backward_demodulation,[],[f110,f199])).

fof(f110,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f197,plain,
    ( ~ spl5_10
    | spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl5_10
    | spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f192,f174])).

fof(f174,plain,
    ( ~ v1_xboole_0(k1_connsp_2(sK0,sK1))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_13
  <=> v1_xboole_0(k1_connsp_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f192,plain,
    ( v1_xboole_0(k1_connsp_2(sK0,sK1))
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f121,f183,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f183,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl5_14
  <=> m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f121,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f184,plain,
    ( spl5_14
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f139,f91,f86,f76,f71,f181])).

fof(f139,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f73,f78,f88,f93,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f175,plain,
    ( ~ spl5_13
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f170,f158,f172])).

fof(f158,plain,
    ( spl5_11
  <=> r2_hidden(sK1,k1_connsp_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f170,plain,
    ( ~ v1_xboole_0(k1_connsp_2(sK0,sK1))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f160,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f160,plain,
    ( r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f161,plain,
    ( spl5_11
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f134,f91,f86,f76,f71,f158])).

fof(f134,plain,
    ( r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f73,f78,f88,f93,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_connsp_2(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f122,plain,
    ( spl5_9
    | spl5_10
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f100,f91,f119,f115])).

fof(f100,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f63,f93])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f111,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f52,f108])).

fof(f52,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
          & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
      & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

fof(f106,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f51,f103])).

fof(f51,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f50,f96])).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f49,f91])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f48,f86])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f47,f81])).

fof(f47,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f76])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f45,f71])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:45:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.43  % (31111)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.45  % (31117)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (31106)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (31108)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (31121)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (31107)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (31110)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (31105)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (31115)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (31118)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (31114)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (31119)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (31104)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (31115)Refutation not found, incomplete strategy% (31115)------------------------------
% 0.20/0.49  % (31115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31115)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (31115)Memory used [KB]: 10618
% 0.20/0.49  % (31115)Time elapsed: 0.073 s
% 0.20/0.49  % (31115)------------------------------
% 0.20/0.49  % (31115)------------------------------
% 0.20/0.49  % (31109)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (31116)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.51  % (31120)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (31119)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f633,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f99,f106,f111,f122,f161,f175,f184,f197,f222,f259,f269,f385,f631])).
% 0.20/0.51  fof(f631,plain,(
% 0.20/0.51    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_10 | spl5_17 | ~spl5_20 | ~spl5_22 | ~spl5_33),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f630])).
% 0.20/0.51  fof(f630,plain,(
% 0.20/0.51    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_10 | spl5_17 | ~spl5_20 | ~spl5_22 | ~spl5_33)),
% 0.20/0.51    inference(subsumption_resolution,[],[f629,f221])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | spl5_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f219])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    spl5_17 <=> k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.51  fof(f629,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_10 | ~spl5_20 | ~spl5_22 | ~spl5_33)),
% 0.20/0.51    inference(forward_demodulation,[],[f628,f622])).
% 0.20/0.51  fof(f622,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_10 | ~spl5_20 | ~spl5_33)),
% 0.20/0.51    inference(subsumption_resolution,[],[f618,f390])).
% 0.20/0.51  fof(f390,plain,(
% 0.20/0.51    m1_subset_1(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),u1_struct_0(sK0)) | (~spl5_4 | ~spl5_20 | ~spl5_33)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f88,f258,f384,f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,u1_struct_0(X1)) | ~r2_hidden(X2,k2_pre_topc(X1,X0))) )),
% 0.20/0.51    inference(resolution,[],[f66,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.51  fof(f384,plain,(
% 0.20/0.51    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_33),
% 0.20/0.51    inference(avatar_component_clause,[],[f382])).
% 0.20/0.51  fof(f382,plain,(
% 0.20/0.51    spl5_33 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.20/0.51  fof(f258,plain,(
% 0.20/0.51    r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~spl5_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f256])).
% 0.20/0.51  fof(f256,plain,(
% 0.20/0.51    spl5_20 <=> r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl5_4 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f618,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))))) | ~m1_subset_1(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_10 | ~spl5_20)),
% 0.20/0.51    inference(resolution,[],[f294,f258])).
% 0.20/0.51  fof(f294,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f293,f198])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | (~spl5_5 | spl5_10)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f93,f120,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f65,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl5_10 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl5_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f291,f198])).
% 0.20/0.51  fof(f291,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.51    inference(resolution,[],[f156,f93])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f155,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ~v2_struct_0(sK0) | spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    spl5_1 <=> v2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f154,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl5_2 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f153,f88])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f55,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    v3_tdlat_3(sK0) | ~spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    spl5_3 <=> v3_tdlat_3(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v3_tdlat_3(X0) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).
% 0.20/0.51  fof(f628,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | spl5_10 | ~spl5_20 | ~spl5_22 | ~spl5_33)),
% 0.20/0.51    inference(subsumption_resolution,[],[f624,f390])).
% 0.20/0.51  fof(f624,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))))) | ~m1_subset_1(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | spl5_10 | ~spl5_22)),
% 0.20/0.51    inference(resolution,[],[f296,f268])).
% 0.20/0.51  fof(f268,plain,(
% 0.20/0.51    r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl5_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f266])).
% 0.20/0.51  fof(f266,plain,(
% 0.20/0.51    spl5_22 <=> r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.51  fof(f296,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | spl5_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f295,f199])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | (~spl5_6 | spl5_10)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f98,f120,f69])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl5_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.51  fof(f295,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | spl5_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f292,f199])).
% 0.20/0.51  fof(f292,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.20/0.51    inference(resolution,[],[f156,f98])).
% 0.20/0.51  fof(f385,plain,(
% 0.20/0.51    spl5_33 | ~spl5_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f225,f115,f382])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    spl5_9 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_9),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f117,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f62,f53])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl5_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f115])).
% 0.20/0.51  fof(f269,plain,(
% 0.20/0.51    spl5_22 | ~spl5_5 | ~spl5_6 | spl5_7 | spl5_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f211,f119,f103,f96,f91,f266])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    spl5_7 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_5 | ~spl5_6 | spl5_7 | spl5_10)),
% 0.20/0.51    inference(backward_demodulation,[],[f204,f198])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    r2_hidden(sK4(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_6 | spl5_7 | spl5_10)),
% 0.20/0.51    inference(backward_demodulation,[],[f112,f199])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    r2_hidden(sK4(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_7),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f105,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f103])).
% 0.20/0.51  fof(f259,plain,(
% 0.20/0.51    spl5_20 | ~spl5_5 | ~spl5_6 | spl5_7 | spl5_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f210,f119,f103,f96,f91,f256])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    r2_hidden(sK4(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (~spl5_5 | ~spl5_6 | spl5_7 | spl5_10)),
% 0.20/0.51    inference(backward_demodulation,[],[f205,f198])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    r2_hidden(sK4(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | (~spl5_6 | spl5_7 | spl5_10)),
% 0.20/0.51    inference(backward_demodulation,[],[f113,f199])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    r2_hidden(sK4(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | spl5_7),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f105,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f222,plain,(
% 0.20/0.51    ~spl5_17 | ~spl5_5 | ~spl5_6 | spl5_8 | spl5_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f209,f119,f108,f96,f91,f219])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl5_8 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k2_tarski(sK2,sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | (~spl5_5 | ~spl5_6 | spl5_8 | spl5_10)),
% 0.20/0.51    inference(backward_demodulation,[],[f206,f198])).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | (~spl5_6 | spl5_8 | spl5_10)),
% 0.20/0.51    inference(backward_demodulation,[],[f110,f199])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | spl5_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f108])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    ~spl5_10 | spl5_13 | ~spl5_14),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f196])).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    $false | (~spl5_10 | spl5_13 | ~spl5_14)),
% 0.20/0.51    inference(subsumption_resolution,[],[f192,f174])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_connsp_2(sK0,sK1)) | spl5_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f172])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    spl5_13 <=> v1_xboole_0(k1_connsp_2(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    v1_xboole_0(k1_connsp_2(sK0,sK1)) | (~spl5_10 | ~spl5_14)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f121,f183,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f181])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    spl5_14 <=> m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f119])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl5_14 | spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f139,f91,f86,f76,f71,f181])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f73,f78,f88,f93,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    ~spl5_13 | ~spl5_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f170,f158,f172])).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    spl5_11 <=> r2_hidden(sK1,k1_connsp_2(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_connsp_2(sK0,sK1)) | ~spl5_11),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f160,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(rectify,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_connsp_2(sK0,sK1)) | ~spl5_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f158])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    spl5_11 | spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f134,f91,f86,f76,f71,f158])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_connsp_2(sK0,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f73,f78,f88,f93,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | r2_hidden(X1,k1_connsp_2(X0,X1)) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl5_9 | spl5_10 | ~spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f100,f91,f119,f115])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 0.20/0.51    inference(resolution,[],[f63,f93])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ~spl5_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f52,f108])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f37,f36,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ~spl5_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f51,f103])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    spl5_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f96])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f91])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f86])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f81])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v3_tdlat_3(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f76])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ~spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f71])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (31119)------------------------------
% 0.20/0.51  % (31119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31119)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (31119)Memory used [KB]: 11129
% 0.20/0.51  % (31119)Time elapsed: 0.104 s
% 0.20/0.51  % (31119)------------------------------
% 0.20/0.51  % (31119)------------------------------
% 0.20/0.51  % (31112)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (31102)Success in time 0.165 s
%------------------------------------------------------------------------------
