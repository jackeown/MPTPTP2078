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
% DateTime   : Thu Dec  3 13:13:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 170 expanded)
%              Number of leaves         :   28 (  78 expanded)
%              Depth                    :    7
%              Number of atoms          :  255 ( 461 expanded)
%              Number of equality atoms :   39 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f511,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f77,f96,f103,f109,f124,f147,f186,f199,f258,f263,f507,f510])).

fof(f510,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f507,plain,
    ( spl2_68
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f494,f194,f55,f497])).

fof(f497,plain,
    ( spl2_68
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f55,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f194,plain,
    ( spl2_24
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f494,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(superposition,[],[f97,f196])).

fof(f196,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f97,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f57,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f57,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f263,plain,
    ( spl2_33
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f251,f100,f260])).

fof(f260,plain,
    ( spl2_33
  <=> k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f100,plain,
    ( spl2_10
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f251,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f102,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f102,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f258,plain,
    ( spl2_32
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f252,f100,f255])).

fof(f255,plain,
    ( spl2_32
  <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f252,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f102,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f199,plain,
    ( spl2_24
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f197,f183,f144,f194])).

fof(f144,plain,
    ( spl2_16
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f183,plain,
    ( spl2_22
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f197,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(backward_demodulation,[],[f146,f185])).

fof(f185,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f146,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f186,plain,
    ( spl2_22
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f181,f121,f106,f60,f183])).

fof(f60,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f106,plain,
    ( spl2_11
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f121,plain,
    ( spl2_13
  <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f181,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f149,f123])).

fof(f123,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f149,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f62,f108,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f108,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f62,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f147,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f141,f60,f55,f144])).

% (2565)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f141,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f62,f57,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f124,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f118,f60,f55,f50,f121])).

fof(f50,plain,
    ( spl2_2
  <=> v5_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f118,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f62,f52,f57,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f52,plain,
    ( v5_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f109,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f104,f60,f55,f106])).

fof(f104,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f62,f57,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f103,plain,
    ( spl2_10
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f98,f93,f100])).

fof(f93,plain,
    ( spl2_9
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f98,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f95,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f95,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f96,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f91,f60,f55,f93])).

fof(f91,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f62,f57,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f77,plain,
    ( ~ spl2_6
    | spl2_1 ),
    inference(avatar_split_clause,[],[f71,f45,f73])).

fof(f73,plain,
    ( spl2_6
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f45,plain,
    ( spl2_1
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f71,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | spl2_1 ),
    inference(resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f63,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
        & v5_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      & v5_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

fof(f58,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f32,f45])).

fof(f32,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (2542)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.49  % (2548)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.50  % (2541)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.51  % (2558)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.51  % (2560)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.19/0.51  % (2561)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.51  % (2546)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.52  % (2556)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.52  % (2546)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f511,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f77,f96,f103,f109,f124,f147,f186,f199,f258,f263,f507,f510])).
% 0.19/0.52  fof(f510,plain,(
% 0.19/0.52    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) | ~m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 0.19/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.52  fof(f507,plain,(
% 0.19/0.52    spl2_68 | ~spl2_3 | ~spl2_24),
% 0.19/0.52    inference(avatar_split_clause,[],[f494,f194,f55,f497])).
% 1.32/0.52  fof(f497,plain,(
% 1.32/0.52    spl2_68 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 1.32/0.52  fof(f55,plain,(
% 1.32/0.52    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.32/0.52  fof(f194,plain,(
% 1.32/0.52    spl2_24 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.32/0.52  fof(f494,plain,(
% 1.32/0.52    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_24)),
% 1.32/0.52    inference(superposition,[],[f97,f196])).
% 1.32/0.52  fof(f196,plain,(
% 1.32/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_24),
% 1.32/0.52    inference(avatar_component_clause,[],[f194])).
% 1.32/0.52  fof(f97,plain,(
% 1.32/0.52    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_3),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f57,f41])).
% 1.32/0.52  fof(f41,plain,(
% 1.32/0.52    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.52    inference(cnf_transformation,[],[f21])).
% 1.32/0.52  fof(f21,plain,(
% 1.32/0.52    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.52    inference(ennf_transformation,[],[f3])).
% 1.32/0.52  fof(f3,axiom,(
% 1.32/0.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.32/0.52  fof(f57,plain,(
% 1.32/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.32/0.52    inference(avatar_component_clause,[],[f55])).
% 1.32/0.52  fof(f263,plain,(
% 1.32/0.52    spl2_33 | ~spl2_10),
% 1.32/0.52    inference(avatar_split_clause,[],[f251,f100,f260])).
% 1.32/0.52  fof(f260,plain,(
% 1.32/0.52    spl2_33 <=> k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 1.32/0.52  fof(f100,plain,(
% 1.32/0.52    spl2_10 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.32/0.52  fof(f251,plain,(
% 1.32/0.52    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_10),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f102,f42])).
% 1.32/0.52  fof(f42,plain,(
% 1.32/0.52    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.52    inference(cnf_transformation,[],[f22])).
% 1.32/0.52  fof(f22,plain,(
% 1.32/0.52    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.52    inference(ennf_transformation,[],[f1])).
% 1.32/0.52  fof(f1,axiom,(
% 1.32/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.32/0.52  fof(f102,plain,(
% 1.32/0.52    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_10),
% 1.32/0.52    inference(avatar_component_clause,[],[f100])).
% 1.32/0.52  fof(f258,plain,(
% 1.32/0.52    spl2_32 | ~spl2_10),
% 1.32/0.52    inference(avatar_split_clause,[],[f252,f100,f255])).
% 1.32/0.52  fof(f255,plain,(
% 1.32/0.52    spl2_32 <=> m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 1.32/0.52  fof(f252,plain,(
% 1.32/0.52    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl2_10),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f102,f43])).
% 1.32/0.52  fof(f43,plain,(
% 1.32/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.52    inference(cnf_transformation,[],[f23])).
% 1.32/0.52  fof(f23,plain,(
% 1.32/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.52    inference(ennf_transformation,[],[f2])).
% 1.32/0.52  fof(f2,axiom,(
% 1.32/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.32/0.52  fof(f199,plain,(
% 1.32/0.52    spl2_24 | ~spl2_16 | ~spl2_22),
% 1.32/0.52    inference(avatar_split_clause,[],[f197,f183,f144,f194])).
% 1.32/0.52  fof(f144,plain,(
% 1.32/0.52    spl2_16 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.32/0.52  fof(f183,plain,(
% 1.32/0.52    spl2_22 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.32/0.52  fof(f197,plain,(
% 1.32/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_16 | ~spl2_22)),
% 1.32/0.52    inference(backward_demodulation,[],[f146,f185])).
% 1.32/0.52  fof(f185,plain,(
% 1.32/0.52    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_22),
% 1.32/0.52    inference(avatar_component_clause,[],[f183])).
% 1.32/0.52  fof(f146,plain,(
% 1.32/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_16),
% 1.32/0.52    inference(avatar_component_clause,[],[f144])).
% 1.32/0.52  fof(f186,plain,(
% 1.32/0.52    spl2_22 | ~spl2_4 | ~spl2_11 | ~spl2_13),
% 1.32/0.52    inference(avatar_split_clause,[],[f181,f121,f106,f60,f183])).
% 1.32/0.52  fof(f60,plain,(
% 1.32/0.52    spl2_4 <=> l1_pre_topc(sK0)),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.32/0.52  fof(f106,plain,(
% 1.32/0.52    spl2_11 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.32/0.52  fof(f121,plain,(
% 1.32/0.52    spl2_13 <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.32/0.52  fof(f181,plain,(
% 1.32/0.52    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_4 | ~spl2_11 | ~spl2_13)),
% 1.32/0.52    inference(forward_demodulation,[],[f149,f123])).
% 1.32/0.52  fof(f123,plain,(
% 1.32/0.52    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~spl2_13),
% 1.32/0.52    inference(avatar_component_clause,[],[f121])).
% 1.32/0.52  fof(f149,plain,(
% 1.32/0.52    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_11)),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f62,f108,f36])).
% 1.32/0.52  fof(f36,plain,(
% 1.32/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f16])).
% 1.32/0.52  fof(f16,plain,(
% 1.32/0.52    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.32/0.52    inference(flattening,[],[f15])).
% 1.32/0.52  fof(f15,plain,(
% 1.32/0.52    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.32/0.52    inference(ennf_transformation,[],[f5])).
% 1.32/0.52  fof(f5,axiom,(
% 1.32/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 1.32/0.52  fof(f108,plain,(
% 1.32/0.52    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 1.32/0.52    inference(avatar_component_clause,[],[f106])).
% 1.32/0.52  fof(f62,plain,(
% 1.32/0.52    l1_pre_topc(sK0) | ~spl2_4),
% 1.32/0.52    inference(avatar_component_clause,[],[f60])).
% 1.32/0.52  fof(f147,plain,(
% 1.32/0.52    spl2_16 | ~spl2_3 | ~spl2_4),
% 1.32/0.52    inference(avatar_split_clause,[],[f141,f60,f55,f144])).
% 1.32/0.52  % (2565)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.32/0.52  fof(f141,plain,(
% 1.32/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f62,f57,f39])).
% 1.32/0.52  fof(f39,plain,(
% 1.32/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.32/0.52    inference(cnf_transformation,[],[f18])).
% 1.32/0.52  fof(f18,plain,(
% 1.32/0.52    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.52    inference(ennf_transformation,[],[f8])).
% 1.32/0.52  fof(f8,axiom,(
% 1.32/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.32/0.52  fof(f124,plain,(
% 1.32/0.52    spl2_13 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 1.32/0.52    inference(avatar_split_clause,[],[f118,f60,f55,f50,f121])).
% 1.32/0.52  fof(f50,plain,(
% 1.32/0.52    spl2_2 <=> v5_tops_1(sK1,sK0)),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.32/0.52  fof(f118,plain,(
% 1.32/0.52    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f62,f52,f57,f37])).
% 1.32/0.52  fof(f37,plain,(
% 1.32/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) )),
% 1.32/0.52    inference(cnf_transformation,[],[f28])).
% 1.32/0.52  fof(f28,plain,(
% 1.32/0.52    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.52    inference(nnf_transformation,[],[f17])).
% 1.32/0.52  fof(f17,plain,(
% 1.32/0.52    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.52    inference(ennf_transformation,[],[f6])).
% 1.32/0.52  fof(f6,axiom,(
% 1.32/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 1.32/0.52  fof(f52,plain,(
% 1.32/0.52    v5_tops_1(sK1,sK0) | ~spl2_2),
% 1.32/0.52    inference(avatar_component_clause,[],[f50])).
% 1.32/0.52  fof(f109,plain,(
% 1.32/0.52    spl2_11 | ~spl2_3 | ~spl2_4),
% 1.32/0.52    inference(avatar_split_clause,[],[f104,f60,f55,f106])).
% 1.32/0.52  fof(f104,plain,(
% 1.32/0.52    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_4)),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f62,f57,f40])).
% 1.32/0.52  fof(f40,plain,(
% 1.32/0.52    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f20])).
% 1.32/0.52  fof(f20,plain,(
% 1.32/0.52    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.32/0.52    inference(flattening,[],[f19])).
% 1.32/0.52  fof(f19,plain,(
% 1.32/0.52    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.32/0.52    inference(ennf_transformation,[],[f7])).
% 1.32/0.52  fof(f7,axiom,(
% 1.32/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.32/0.52  fof(f103,plain,(
% 1.32/0.52    spl2_10 | ~spl2_9),
% 1.32/0.52    inference(avatar_split_clause,[],[f98,f93,f100])).
% 1.32/0.52  fof(f93,plain,(
% 1.32/0.52    spl2_9 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.32/0.52  fof(f98,plain,(
% 1.32/0.52    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_9),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f95,f34])).
% 1.32/0.52  fof(f34,plain,(
% 1.32/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f27])).
% 1.32/0.52  fof(f27,plain,(
% 1.32/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.32/0.52    inference(nnf_transformation,[],[f4])).
% 1.32/0.52  fof(f4,axiom,(
% 1.32/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.32/0.52  fof(f95,plain,(
% 1.32/0.52    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_9),
% 1.32/0.52    inference(avatar_component_clause,[],[f93])).
% 1.32/0.52  fof(f96,plain,(
% 1.32/0.52    spl2_9 | ~spl2_3 | ~spl2_4),
% 1.32/0.52    inference(avatar_split_clause,[],[f91,f60,f55,f93])).
% 1.32/0.52  fof(f91,plain,(
% 1.32/0.52    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f62,f57,f35])).
% 1.32/0.52  fof(f35,plain,(
% 1.32/0.52    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f14])).
% 1.32/0.52  fof(f14,plain,(
% 1.32/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.52    inference(ennf_transformation,[],[f9])).
% 1.32/0.52  fof(f9,axiom,(
% 1.32/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.32/0.52  fof(f77,plain,(
% 1.32/0.52    ~spl2_6 | spl2_1),
% 1.32/0.52    inference(avatar_split_clause,[],[f71,f45,f73])).
% 1.32/0.52  fof(f73,plain,(
% 1.32/0.52    spl2_6 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.32/0.52  fof(f45,plain,(
% 1.32/0.52    spl2_1 <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 1.32/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.32/0.52  fof(f71,plain,(
% 1.32/0.52    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) | spl2_1),
% 1.32/0.52    inference(resolution,[],[f47,f33])).
% 1.32/0.52  fof(f33,plain,(
% 1.32/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.32/0.52    inference(cnf_transformation,[],[f27])).
% 1.32/0.52  fof(f47,plain,(
% 1.32/0.52    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | spl2_1),
% 1.32/0.52    inference(avatar_component_clause,[],[f45])).
% 1.32/0.52  fof(f63,plain,(
% 1.32/0.52    spl2_4),
% 1.32/0.52    inference(avatar_split_clause,[],[f29,f60])).
% 1.32/0.52  fof(f29,plain,(
% 1.32/0.52    l1_pre_topc(sK0)),
% 1.32/0.52    inference(cnf_transformation,[],[f26])).
% 1.32/0.52  fof(f26,plain,(
% 1.32/0.52    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.32/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).
% 1.32/0.52  fof(f24,plain,(
% 1.32/0.52    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.32/0.52    introduced(choice_axiom,[])).
% 1.32/0.52  fof(f25,plain,(
% 1.32/0.52    ? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.32/0.52    introduced(choice_axiom,[])).
% 1.32/0.52  fof(f13,plain,(
% 1.32/0.52    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.32/0.52    inference(flattening,[],[f12])).
% 1.32/0.52  fof(f12,plain,(
% 1.32/0.52    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.32/0.52    inference(ennf_transformation,[],[f11])).
% 1.32/0.52  fof(f11,negated_conjecture,(
% 1.32/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 1.32/0.52    inference(negated_conjecture,[],[f10])).
% 1.32/0.52  fof(f10,conjecture,(
% 1.32/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 1.32/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).
% 1.32/0.52  fof(f58,plain,(
% 1.32/0.52    spl2_3),
% 1.32/0.52    inference(avatar_split_clause,[],[f30,f55])).
% 1.32/0.52  fof(f30,plain,(
% 1.32/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.52    inference(cnf_transformation,[],[f26])).
% 1.32/0.52  fof(f53,plain,(
% 1.32/0.52    spl2_2),
% 1.32/0.52    inference(avatar_split_clause,[],[f31,f50])).
% 1.32/0.52  fof(f31,plain,(
% 1.32/0.52    v5_tops_1(sK1,sK0)),
% 1.32/0.52    inference(cnf_transformation,[],[f26])).
% 1.32/0.52  fof(f48,plain,(
% 1.32/0.52    ~spl2_1),
% 1.32/0.52    inference(avatar_split_clause,[],[f32,f45])).
% 1.32/0.52  fof(f32,plain,(
% 1.32/0.52    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 1.32/0.52    inference(cnf_transformation,[],[f26])).
% 1.32/0.52  % SZS output end Proof for theBenchmark
% 1.32/0.52  % (2546)------------------------------
% 1.32/0.52  % (2546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.52  % (2546)Termination reason: Refutation
% 1.32/0.52  
% 1.32/0.52  % (2546)Memory used [KB]: 11001
% 1.32/0.52  % (2546)Time elapsed: 0.083 s
% 1.32/0.52  % (2546)------------------------------
% 1.32/0.52  % (2546)------------------------------
% 1.32/0.52  % (2549)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.32/0.52  % (2535)Success in time 0.17 s
%------------------------------------------------------------------------------
