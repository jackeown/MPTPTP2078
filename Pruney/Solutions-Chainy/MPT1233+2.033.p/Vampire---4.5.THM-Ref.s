%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 156 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 324 expanded)
%              Number of equality atoms :   52 (  97 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f77,f82,f108,f123,f137])).

fof(f137,plain,
    ( spl1_4
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl1_4
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f135,f122])).

fof(f122,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl1_7
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f135,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | spl1_4
    | ~ spl1_5 ),
    inference(backward_demodulation,[],[f76,f134])).

fof(f134,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f133,f54])).

fof(f54,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f133,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl1_5 ),
    inference(backward_demodulation,[],[f87,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f81,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(resolution,[],[f49,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f81,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl1_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f87,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f81,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

fof(f76,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl1_4
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f123,plain,
    ( spl1_7
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f118,f105,f63,f120])).

fof(f63,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f105,plain,
    ( spl1_6
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f118,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f117,f54])).

fof(f117,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(backward_demodulation,[],[f114,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f65,f40,f107,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f107,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f114,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl1_2 ),
    inference(forward_demodulation,[],[f112,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f92,f54])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f112,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f65,f56,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f55,f54])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f108,plain,
    ( spl1_6
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f100,f68,f63,f58,f105])).

fof(f58,plain,
    ( spl1_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f68,plain,
    ( spl1_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f100,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f60,f65,f70,f40,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f70,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f60,plain,
    ( v2_pre_topc(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f82,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f72,f63,f79])).

fof(f72,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f65,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f77,plain,(
    ~ spl1_4 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f71,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f37,f68])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:34:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (3998)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.44  % (3998)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f61,f66,f71,f77,f82,f108,f123,f137])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    spl1_4 | ~spl1_5 | ~spl1_7),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    $false | (spl1_4 | ~spl1_5 | ~spl1_7)),
% 0.21/0.44    inference(subsumption_resolution,[],[f135,f122])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | ~spl1_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f120])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    spl1_7 <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | (spl1_4 | ~spl1_5)),
% 0.21/0.44    inference(backward_demodulation,[],[f76,f134])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl1_5),
% 0.21/0.44    inference(forward_demodulation,[],[f133,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f39,f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f42,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~spl1_5),
% 0.21/0.44    inference(backward_demodulation,[],[f87,f129])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    k1_xboole_0 = k1_struct_0(sK0) | ~spl1_5),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f81,f85])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.44    inference(resolution,[],[f49,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    l1_struct_0(sK0) | ~spl1_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f79])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl1_5 <=> l1_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) | ~spl1_5),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f81,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) | spl1_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl1_4 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    spl1_7 | ~spl1_2 | ~spl1_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f118,f105,f63,f120])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl1_2 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    spl1_6 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | (~spl1_2 | ~spl1_6)),
% 0.21/0.44    inference(forward_demodulation,[],[f117,f54])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k1_tops_1(sK0,u1_struct_0(sK0)) | (~spl1_2 | ~spl1_6)),
% 0.21/0.44    inference(backward_demodulation,[],[f114,f116])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | (~spl1_2 | ~spl1_6)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f65,f40,f107,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    v4_pre_topc(k1_xboole_0,sK0) | ~spl1_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f105])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    l1_pre_topc(sK0) | ~spl1_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f63])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) | ~spl1_2),
% 0.21/0.44    inference(forward_demodulation,[],[f112,f96])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f92,f54])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f40,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl1_2),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f65,f56,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f55,f54])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f41,f53])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    spl1_6 | ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f100,f68,f63,f58,f105])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    spl1_1 <=> v2_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl1_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    v4_pre_topc(k1_xboole_0,sK0) | (~spl1_1 | ~spl1_2 | ~spl1_3)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f60,f65,f70,f40,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0) | ~spl1_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f68])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    v2_pre_topc(sK0) | ~spl1_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f58])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl1_5 | ~spl1_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f72,f63,f79])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    l1_struct_0(sK0) | ~spl1_2),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f65,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ~spl1_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f36,f74])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.44    inference(negated_conjecture,[],[f16])).
% 0.21/0.44  fof(f16,conjecture,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl1_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f68])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    spl1_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f35,f63])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl1_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f34,f58])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    v2_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (3998)------------------------------
% 0.21/0.44  % (3998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (3998)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (3998)Memory used [KB]: 10618
% 0.21/0.44  % (3998)Time elapsed: 0.010 s
% 0.21/0.44  % (3998)------------------------------
% 0.21/0.44  % (3998)------------------------------
% 0.21/0.44  % (3981)Success in time 0.08 s
%------------------------------------------------------------------------------
