%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:48 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 236 expanded)
%              Number of leaves         :   36 (  99 expanded)
%              Depth                    :    9
%              Number of atoms          :  438 ( 922 expanded)
%              Number of equality atoms :   78 ( 168 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8390)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f323,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f113,f118,f127,f129,f140,f150,f161,f176,f220,f230,f237,f254,f260,f285,f291,f307,f314,f322])).

fof(f322,plain,
    ( ~ spl11_14
    | ~ spl11_2
    | ~ spl11_32
    | ~ spl11_9
    | ~ spl11_29
    | spl11_36 ),
    inference(avatar_split_clause,[],[f318,f311,f234,f120,f288,f84,f158])).

fof(f158,plain,
    ( spl11_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f84,plain,
    ( spl11_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f288,plain,
    ( spl11_32
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f120,plain,
    ( spl11_9
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f234,plain,
    ( spl11_29
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f311,plain,
    ( spl11_36
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f318,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl11_29
    | spl11_36 ),
    inference(forward_demodulation,[],[f316,f236])).

fof(f236,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f234])).

fof(f316,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl11_36 ),
    inference(resolution,[],[f315,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK5),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK4)) )
    | spl11_36 ),
    inference(resolution,[],[f313,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f313,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl11_36 ),
    inference(avatar_component_clause,[],[f311])).

fof(f314,plain,
    ( ~ spl11_11
    | ~ spl11_36
    | ~ spl11_1
    | ~ spl11_13
    | spl11_35 ),
    inference(avatar_split_clause,[],[f309,f304,f147,f79,f311,f137])).

fof(f137,plain,
    ( spl11_11
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f79,plain,
    ( spl11_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f147,plain,
    ( spl11_13
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f304,plain,
    ( spl11_35
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f309,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl11_35 ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl11_35 ),
    inference(superposition,[],[f306,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f306,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl11_35 ),
    inference(avatar_component_clause,[],[f304])).

fof(f307,plain,
    ( spl11_3
    | spl11_5
    | ~ spl11_17
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_1
    | ~ spl11_8
    | ~ spl11_6
    | ~ spl11_2
    | ~ spl11_35
    | spl11_26 ),
    inference(avatar_split_clause,[],[f292,f217,f304,f84,f104,f115,f79,f110,f94,f173,f99,f89])).

fof(f89,plain,
    ( spl11_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f99,plain,
    ( spl11_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f173,plain,
    ( spl11_17
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f94,plain,
    ( spl11_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f110,plain,
    ( spl11_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f115,plain,
    ( spl11_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f104,plain,
    ( spl11_6
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f217,plain,
    ( spl11_26
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f292,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | k1_xboole_0 = sK1
    | v1_xboole_0(sK2)
    | spl11_26 ),
    inference(superposition,[],[f219,f57])).

% (8371)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (8369)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (8371)Refutation not found, incomplete strategy% (8371)------------------------------
% (8371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8371)Termination reason: Refutation not found, incomplete strategy

% (8371)Memory used [KB]: 10874
% (8371)Time elapsed: 0.150 s
% (8371)------------------------------
% (8371)------------------------------
% (8363)Refutation not found, incomplete strategy% (8363)------------------------------
% (8363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8363)Termination reason: Refutation not found, incomplete strategy

% (8363)Memory used [KB]: 11129
% (8363)Time elapsed: 0.145 s
% (8363)------------------------------
% (8363)------------------------------
fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f219,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl11_26 ),
    inference(avatar_component_clause,[],[f217])).

fof(f291,plain,
    ( ~ spl11_7
    | spl11_32
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f286,f282,f288,f110])).

fof(f282,plain,
    ( spl11_31
  <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f286,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl11_31 ),
    inference(superposition,[],[f284,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f284,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f282])).

fof(f285,plain,
    ( ~ spl11_8
    | spl11_31
    | ~ spl11_17 ),
    inference(avatar_split_clause,[],[f177,f173,f282,f115])).

fof(f177,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl11_17 ),
    inference(superposition,[],[f175,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f175,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f173])).

fof(f260,plain,(
    spl11_30 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl11_30 ),
    inference(unit_resulting_resolution,[],[f51,f256])).

fof(f256,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | spl11_30 ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | spl11_30 ),
    inference(superposition,[],[f253,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f253,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl11_30 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl11_30
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f51,plain,(
    ! [X0] : v1_xboole_0(sK9(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f254,plain,
    ( ~ spl11_30
    | spl11_3
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f238,f227,f89,f251])).

fof(f227,plain,
    ( spl11_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f238,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl11_3
    | ~ spl11_28 ),
    inference(backward_demodulation,[],[f91,f229])).

fof(f229,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f227])).

fof(f91,plain,
    ( ~ v1_xboole_0(sK2)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f237,plain,
    ( ~ spl11_8
    | spl11_29
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f231,f223,f234,f115])).

fof(f223,plain,
    ( spl11_27
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f231,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl11_27 ),
    inference(superposition,[],[f225,f60])).

fof(f225,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f223])).

fof(f230,plain,
    ( ~ spl11_6
    | spl11_27
    | spl11_28
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f152,f115,f227,f223,f104])).

fof(f152,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ spl11_8 ),
    inference(resolution,[],[f117,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f117,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f220,plain,(
    ~ spl11_26 ),
    inference(avatar_split_clause,[],[f36,f217])).

fof(f36,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f176,plain,(
    spl11_17 ),
    inference(avatar_split_clause,[],[f34,f173])).

fof(f34,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f16])).

fof(f161,plain,
    ( spl11_14
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f155,f115,f158])).

fof(f155,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_8 ),
    inference(resolution,[],[f117,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f150,plain,
    ( spl11_13
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f133,f110,f147])).

fof(f133,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl11_7 ),
    inference(resolution,[],[f112,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f112,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f140,plain,
    ( spl11_11
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f134,f110,f137])).

fof(f134,plain,
    ( v1_relat_1(sK4)
    | ~ spl11_7 ),
    inference(resolution,[],[f112,f58])).

fof(f129,plain,
    ( spl11_5
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl11_5
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f101,f126,f43])).

fof(f126,plain,
    ( v1_xboole_0(sK1)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl11_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f101,plain,
    ( k1_xboole_0 != sK1
    | spl11_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f127,plain,
    ( spl11_9
    | spl11_10
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f108,f94,f124,f120])).

fof(f108,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1)
    | ~ spl11_4 ),
    inference(resolution,[],[f96,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f96,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f118,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f41,f115])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f113,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f38,f110])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f107,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f40,f104])).

fof(f40,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f35,f99])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f33,f94])).

fof(f33,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f42,f89])).

fof(f42,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f39,f84])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f37,f79])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (8368)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.45  % (8376)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (8362)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (8364)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (8365)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (8361)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (8363)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (8374)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (8389)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (8381)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (8383)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (8373)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.53  % (8370)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.53  % (8382)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.53  % (8372)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.53  % (8379)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.53  % (8375)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.53  % (8366)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.53  % (8384)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.53  % (8367)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.53  % (8385)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.53  % (8386)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.54  % (8388)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.54  % (8387)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.54  % (8377)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.54  % (8378)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.54  % (8378)Refutation not found, incomplete strategy% (8378)------------------------------
% 1.33/0.54  % (8378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (8378)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (8378)Memory used [KB]: 10746
% 1.33/0.54  % (8378)Time elapsed: 0.142 s
% 1.33/0.54  % (8378)------------------------------
% 1.33/0.54  % (8378)------------------------------
% 1.33/0.54  % (8380)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.54  % (8383)Refutation found. Thanks to Tanya!
% 1.45/0.54  % SZS status Theorem for theBenchmark
% 1.45/0.54  % SZS output start Proof for theBenchmark
% 1.45/0.54  % (8390)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.54  fof(f323,plain,(
% 1.45/0.54    $false),
% 1.45/0.54    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f113,f118,f127,f129,f140,f150,f161,f176,f220,f230,f237,f254,f260,f285,f291,f307,f314,f322])).
% 1.45/0.54  fof(f322,plain,(
% 1.45/0.54    ~spl11_14 | ~spl11_2 | ~spl11_32 | ~spl11_9 | ~spl11_29 | spl11_36),
% 1.45/0.54    inference(avatar_split_clause,[],[f318,f311,f234,f120,f288,f84,f158])).
% 1.45/0.54  fof(f158,plain,(
% 1.45/0.54    spl11_14 <=> v1_relat_1(sK3)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 1.45/0.54  fof(f84,plain,(
% 1.45/0.54    spl11_2 <=> v1_funct_1(sK3)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.45/0.54  fof(f288,plain,(
% 1.45/0.54    spl11_32 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).
% 1.45/0.54  fof(f120,plain,(
% 1.45/0.54    spl11_9 <=> r2_hidden(sK5,sK1)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.45/0.54  fof(f234,plain,(
% 1.45/0.54    spl11_29 <=> sK1 = k1_relat_1(sK3)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).
% 1.45/0.54  fof(f311,plain,(
% 1.45/0.54    spl11_36 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).
% 1.45/0.54  fof(f318,plain,(
% 1.45/0.54    ~r2_hidden(sK5,sK1) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl11_29 | spl11_36)),
% 1.45/0.54    inference(forward_demodulation,[],[f316,f236])).
% 1.45/0.54  fof(f236,plain,(
% 1.45/0.54    sK1 = k1_relat_1(sK3) | ~spl11_29),
% 1.45/0.54    inference(avatar_component_clause,[],[f234])).
% 1.45/0.54  fof(f316,plain,(
% 1.45/0.54    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl11_36),
% 1.45/0.54    inference(resolution,[],[f315,f70])).
% 1.45/0.54  fof(f70,plain,(
% 1.45/0.54    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.45/0.54    inference(equality_resolution,[],[f69])).
% 1.45/0.54  fof(f69,plain,(
% 1.45/0.54    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.45/0.54    inference(equality_resolution,[],[f49])).
% 1.45/0.54  fof(f49,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.45/0.54    inference(cnf_transformation,[],[f19])).
% 1.45/0.54  fof(f19,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.54    inference(flattening,[],[f18])).
% 1.45/0.54  fof(f18,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f5])).
% 1.45/0.54  fof(f5,axiom,(
% 1.45/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.45/0.54  fof(f315,plain,(
% 1.45/0.54    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK5),X0) | ~r1_tarski(X0,k1_relat_1(sK4))) ) | spl11_36),
% 1.45/0.54    inference(resolution,[],[f313,f54])).
% 1.45/0.54  fof(f54,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f24])).
% 1.45/0.54  fof(f24,plain,(
% 1.45/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f1])).
% 1.45/0.54  fof(f1,axiom,(
% 1.45/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.54  fof(f313,plain,(
% 1.45/0.54    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl11_36),
% 1.45/0.54    inference(avatar_component_clause,[],[f311])).
% 1.45/0.54  fof(f314,plain,(
% 1.45/0.54    ~spl11_11 | ~spl11_36 | ~spl11_1 | ~spl11_13 | spl11_35),
% 1.45/0.54    inference(avatar_split_clause,[],[f309,f304,f147,f79,f311,f137])).
% 1.45/0.54  fof(f137,plain,(
% 1.45/0.54    spl11_11 <=> v1_relat_1(sK4)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 1.45/0.54  fof(f79,plain,(
% 1.45/0.54    spl11_1 <=> v1_funct_1(sK4)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.45/0.54  fof(f147,plain,(
% 1.45/0.54    spl11_13 <=> v5_relat_1(sK4,sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.45/0.54  fof(f304,plain,(
% 1.45/0.54    spl11_35 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).
% 1.45/0.54  fof(f309,plain,(
% 1.45/0.54    ~v5_relat_1(sK4,sK0) | ~v1_funct_1(sK4) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl11_35),
% 1.45/0.54    inference(trivial_inequality_removal,[],[f308])).
% 1.45/0.54  fof(f308,plain,(
% 1.45/0.54    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v5_relat_1(sK4,sK0) | ~v1_funct_1(sK4) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl11_35),
% 1.45/0.54    inference(superposition,[],[f306,f53])).
% 1.45/0.54  fof(f53,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f23])).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.54    inference(flattening,[],[f22])).
% 1.45/0.54  fof(f22,plain,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.45/0.54    inference(ennf_transformation,[],[f11])).
% 1.45/0.54  fof(f11,axiom,(
% 1.45/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 1.45/0.54  fof(f306,plain,(
% 1.45/0.54    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl11_35),
% 1.45/0.54    inference(avatar_component_clause,[],[f304])).
% 1.45/0.54  fof(f307,plain,(
% 1.45/0.54    spl11_3 | spl11_5 | ~spl11_17 | ~spl11_4 | ~spl11_7 | ~spl11_1 | ~spl11_8 | ~spl11_6 | ~spl11_2 | ~spl11_35 | spl11_26),
% 1.45/0.54    inference(avatar_split_clause,[],[f292,f217,f304,f84,f104,f115,f79,f110,f94,f173,f99,f89])).
% 1.45/0.54  fof(f89,plain,(
% 1.45/0.54    spl11_3 <=> v1_xboole_0(sK2)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.45/0.54  fof(f99,plain,(
% 1.45/0.54    spl11_5 <=> k1_xboole_0 = sK1),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.45/0.54  fof(f173,plain,(
% 1.45/0.54    spl11_17 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 1.45/0.54  fof(f94,plain,(
% 1.45/0.54    spl11_4 <=> m1_subset_1(sK5,sK1)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.45/0.54  fof(f110,plain,(
% 1.45/0.54    spl11_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.45/0.54  fof(f115,plain,(
% 1.45/0.54    spl11_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.45/0.54  fof(f104,plain,(
% 1.45/0.54    spl11_6 <=> v1_funct_2(sK3,sK1,sK2)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.45/0.54  fof(f217,plain,(
% 1.45/0.54    spl11_26 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).
% 1.45/0.54  fof(f292,plain,(
% 1.45/0.54    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(sK5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | k1_xboole_0 = sK1 | v1_xboole_0(sK2) | spl11_26),
% 1.45/0.54    inference(superposition,[],[f219,f57])).
% 1.45/0.55  % (8371)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.55  % (8369)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.55  % (8371)Refutation not found, incomplete strategy% (8371)------------------------------
% 1.45/0.55  % (8371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (8371)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (8371)Memory used [KB]: 10874
% 1.45/0.55  % (8371)Time elapsed: 0.150 s
% 1.45/0.55  % (8371)------------------------------
% 1.45/0.55  % (8371)------------------------------
% 1.45/0.56  % (8363)Refutation not found, incomplete strategy% (8363)------------------------------
% 1.45/0.56  % (8363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (8363)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (8363)Memory used [KB]: 11129
% 1.45/0.56  % (8363)Time elapsed: 0.145 s
% 1.45/0.56  % (8363)------------------------------
% 1.45/0.56  % (8363)------------------------------
% 1.45/0.56  fof(f57,plain,(
% 1.45/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | v1_xboole_0(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f26])).
% 1.45/0.56  fof(f26,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 1.45/0.56    inference(flattening,[],[f25])).
% 1.45/0.56  fof(f25,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 1.45/0.56    inference(ennf_transformation,[],[f12])).
% 1.45/0.56  fof(f12,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 1.45/0.56  fof(f219,plain,(
% 1.45/0.56    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl11_26),
% 1.45/0.56    inference(avatar_component_clause,[],[f217])).
% 1.45/0.56  fof(f291,plain,(
% 1.45/0.56    ~spl11_7 | spl11_32 | ~spl11_31),
% 1.45/0.56    inference(avatar_split_clause,[],[f286,f282,f288,f110])).
% 1.45/0.56  fof(f282,plain,(
% 1.45/0.56    spl11_31 <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 1.45/0.56  fof(f286,plain,(
% 1.45/0.56    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl11_31),
% 1.45/0.56    inference(superposition,[],[f284,f60])).
% 1.45/0.56  fof(f60,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f29])).
% 1.45/0.56  fof(f29,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f8])).
% 1.45/0.56  fof(f8,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.45/0.56  fof(f284,plain,(
% 1.45/0.56    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl11_31),
% 1.45/0.56    inference(avatar_component_clause,[],[f282])).
% 1.45/0.56  fof(f285,plain,(
% 1.45/0.56    ~spl11_8 | spl11_31 | ~spl11_17),
% 1.45/0.56    inference(avatar_split_clause,[],[f177,f173,f282,f115])).
% 1.45/0.56  fof(f177,plain,(
% 1.45/0.56    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl11_17),
% 1.45/0.56    inference(superposition,[],[f175,f59])).
% 1.45/0.56  fof(f59,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f28])).
% 1.45/0.56  fof(f28,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.56    inference(ennf_transformation,[],[f9])).
% 1.45/0.56  fof(f9,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.45/0.56  fof(f175,plain,(
% 1.45/0.56    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl11_17),
% 1.45/0.56    inference(avatar_component_clause,[],[f173])).
% 1.45/0.56  fof(f260,plain,(
% 1.45/0.56    spl11_30),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f257])).
% 1.45/0.56  fof(f257,plain,(
% 1.45/0.56    $false | spl11_30),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f51,f256])).
% 1.45/0.56  fof(f256,plain,(
% 1.45/0.56    ( ! [X0] : (~v1_xboole_0(X0)) ) | spl11_30),
% 1.45/0.56    inference(duplicate_literal_removal,[],[f255])).
% 1.45/0.56  fof(f255,plain,(
% 1.45/0.56    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_xboole_0(X0)) ) | spl11_30),
% 1.45/0.56    inference(superposition,[],[f253,f43])).
% 1.45/0.56  fof(f43,plain,(
% 1.45/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,plain,(
% 1.45/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f2])).
% 1.45/0.56  fof(f2,axiom,(
% 1.45/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.45/0.56  fof(f253,plain,(
% 1.45/0.56    ~v1_xboole_0(k1_xboole_0) | spl11_30),
% 1.45/0.56    inference(avatar_component_clause,[],[f251])).
% 1.45/0.56  fof(f251,plain,(
% 1.45/0.56    spl11_30 <=> v1_xboole_0(k1_xboole_0)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
% 1.45/0.56  fof(f51,plain,(
% 1.45/0.56    ( ! [X0] : (v1_xboole_0(sK9(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f3])).
% 1.45/0.56  fof(f3,axiom,(
% 1.45/0.56    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.45/0.56  fof(f254,plain,(
% 1.45/0.56    ~spl11_30 | spl11_3 | ~spl11_28),
% 1.45/0.56    inference(avatar_split_clause,[],[f238,f227,f89,f251])).
% 1.45/0.56  fof(f227,plain,(
% 1.45/0.56    spl11_28 <=> k1_xboole_0 = sK2),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).
% 1.45/0.56  fof(f238,plain,(
% 1.45/0.56    ~v1_xboole_0(k1_xboole_0) | (spl11_3 | ~spl11_28)),
% 1.45/0.56    inference(backward_demodulation,[],[f91,f229])).
% 1.45/0.57  fof(f229,plain,(
% 1.45/0.57    k1_xboole_0 = sK2 | ~spl11_28),
% 1.45/0.57    inference(avatar_component_clause,[],[f227])).
% 1.45/0.57  fof(f91,plain,(
% 1.45/0.57    ~v1_xboole_0(sK2) | spl11_3),
% 1.45/0.57    inference(avatar_component_clause,[],[f89])).
% 1.45/0.57  fof(f237,plain,(
% 1.45/0.57    ~spl11_8 | spl11_29 | ~spl11_27),
% 1.45/0.57    inference(avatar_split_clause,[],[f231,f223,f234,f115])).
% 1.45/0.57  fof(f223,plain,(
% 1.45/0.57    spl11_27 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).
% 1.45/0.57  fof(f231,plain,(
% 1.45/0.57    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl11_27),
% 1.45/0.57    inference(superposition,[],[f225,f60])).
% 1.45/0.57  fof(f225,plain,(
% 1.45/0.57    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl11_27),
% 1.45/0.57    inference(avatar_component_clause,[],[f223])).
% 1.45/0.57  fof(f230,plain,(
% 1.45/0.57    ~spl11_6 | spl11_27 | spl11_28 | ~spl11_8),
% 1.45/0.57    inference(avatar_split_clause,[],[f152,f115,f227,f223,f104])).
% 1.45/0.57  fof(f152,plain,(
% 1.45/0.57    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~spl11_8),
% 1.45/0.57    inference(resolution,[],[f117,f68])).
% 1.45/0.57  fof(f68,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f32])).
% 1.45/0.57  fof(f32,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.57    inference(flattening,[],[f31])).
% 1.45/0.57  fof(f31,plain,(
% 1.45/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.57    inference(ennf_transformation,[],[f10])).
% 1.45/0.57  fof(f10,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.45/0.57  fof(f117,plain,(
% 1.45/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl11_8),
% 1.45/0.57    inference(avatar_component_clause,[],[f115])).
% 1.45/0.57  fof(f220,plain,(
% 1.45/0.57    ~spl11_26),
% 1.45/0.57    inference(avatar_split_clause,[],[f36,f217])).
% 1.45/0.57  fof(f36,plain,(
% 1.45/0.57    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f16,plain,(
% 1.45/0.57    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.45/0.57    inference(flattening,[],[f15])).
% 1.45/0.57  fof(f15,plain,(
% 1.45/0.57    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.45/0.57    inference(ennf_transformation,[],[f14])).
% 1.45/0.57  fof(f14,negated_conjecture,(
% 1.45/0.57    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.45/0.57    inference(negated_conjecture,[],[f13])).
% 1.45/0.57  fof(f13,conjecture,(
% 1.45/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 1.45/0.57  fof(f176,plain,(
% 1.45/0.57    spl11_17),
% 1.45/0.57    inference(avatar_split_clause,[],[f34,f173])).
% 1.45/0.57  fof(f34,plain,(
% 1.45/0.57    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f161,plain,(
% 1.45/0.57    spl11_14 | ~spl11_8),
% 1.45/0.57    inference(avatar_split_clause,[],[f155,f115,f158])).
% 1.45/0.57  fof(f155,plain,(
% 1.45/0.57    v1_relat_1(sK3) | ~spl11_8),
% 1.45/0.57    inference(resolution,[],[f117,f58])).
% 1.45/0.57  fof(f58,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f27])).
% 1.45/0.57  fof(f27,plain,(
% 1.45/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.57    inference(ennf_transformation,[],[f6])).
% 1.45/0.57  fof(f6,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.45/0.57  fof(f150,plain,(
% 1.45/0.57    spl11_13 | ~spl11_7),
% 1.45/0.57    inference(avatar_split_clause,[],[f133,f110,f147])).
% 1.45/0.57  fof(f133,plain,(
% 1.45/0.57    v5_relat_1(sK4,sK0) | ~spl11_7),
% 1.45/0.57    inference(resolution,[],[f112,f62])).
% 1.45/0.57  fof(f62,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f30])).
% 1.45/0.57  fof(f30,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.57    inference(ennf_transformation,[],[f7])).
% 1.45/0.57  fof(f7,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.45/0.57  fof(f112,plain,(
% 1.45/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl11_7),
% 1.45/0.57    inference(avatar_component_clause,[],[f110])).
% 1.45/0.57  fof(f140,plain,(
% 1.45/0.57    spl11_11 | ~spl11_7),
% 1.45/0.57    inference(avatar_split_clause,[],[f134,f110,f137])).
% 1.45/0.57  fof(f134,plain,(
% 1.45/0.57    v1_relat_1(sK4) | ~spl11_7),
% 1.45/0.57    inference(resolution,[],[f112,f58])).
% 1.45/0.57  fof(f129,plain,(
% 1.45/0.57    spl11_5 | ~spl11_10),
% 1.45/0.57    inference(avatar_contradiction_clause,[],[f128])).
% 1.45/0.57  fof(f128,plain,(
% 1.45/0.57    $false | (spl11_5 | ~spl11_10)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f101,f126,f43])).
% 1.45/0.57  fof(f126,plain,(
% 1.45/0.57    v1_xboole_0(sK1) | ~spl11_10),
% 1.45/0.57    inference(avatar_component_clause,[],[f124])).
% 1.45/0.57  fof(f124,plain,(
% 1.45/0.57    spl11_10 <=> v1_xboole_0(sK1)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.45/0.57  fof(f101,plain,(
% 1.45/0.57    k1_xboole_0 != sK1 | spl11_5),
% 1.45/0.57    inference(avatar_component_clause,[],[f99])).
% 1.45/0.57  fof(f127,plain,(
% 1.45/0.57    spl11_9 | spl11_10 | ~spl11_4),
% 1.45/0.57    inference(avatar_split_clause,[],[f108,f94,f124,f120])).
% 1.45/0.57  fof(f108,plain,(
% 1.45/0.57    v1_xboole_0(sK1) | r2_hidden(sK5,sK1) | ~spl11_4),
% 1.45/0.57    inference(resolution,[],[f96,f52])).
% 1.45/0.57  fof(f52,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f21])).
% 1.45/0.57  fof(f21,plain,(
% 1.45/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.45/0.57    inference(flattening,[],[f20])).
% 1.45/0.57  fof(f20,plain,(
% 1.45/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.45/0.57    inference(ennf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.45/0.57  fof(f96,plain,(
% 1.45/0.57    m1_subset_1(sK5,sK1) | ~spl11_4),
% 1.45/0.57    inference(avatar_component_clause,[],[f94])).
% 1.45/0.57  fof(f118,plain,(
% 1.45/0.57    spl11_8),
% 1.45/0.57    inference(avatar_split_clause,[],[f41,f115])).
% 1.45/0.57  fof(f41,plain,(
% 1.45/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f113,plain,(
% 1.45/0.57    spl11_7),
% 1.45/0.57    inference(avatar_split_clause,[],[f38,f110])).
% 1.45/0.57  fof(f38,plain,(
% 1.45/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f107,plain,(
% 1.45/0.57    spl11_6),
% 1.45/0.57    inference(avatar_split_clause,[],[f40,f104])).
% 1.45/0.57  fof(f40,plain,(
% 1.45/0.57    v1_funct_2(sK3,sK1,sK2)),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f102,plain,(
% 1.45/0.57    ~spl11_5),
% 1.45/0.57    inference(avatar_split_clause,[],[f35,f99])).
% 1.45/0.57  fof(f35,plain,(
% 1.45/0.57    k1_xboole_0 != sK1),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f97,plain,(
% 1.45/0.57    spl11_4),
% 1.45/0.57    inference(avatar_split_clause,[],[f33,f94])).
% 1.45/0.57  fof(f33,plain,(
% 1.45/0.57    m1_subset_1(sK5,sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f92,plain,(
% 1.45/0.57    ~spl11_3),
% 1.45/0.57    inference(avatar_split_clause,[],[f42,f89])).
% 1.45/0.57  fof(f42,plain,(
% 1.45/0.57    ~v1_xboole_0(sK2)),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f87,plain,(
% 1.45/0.57    spl11_2),
% 1.45/0.57    inference(avatar_split_clause,[],[f39,f84])).
% 1.45/0.57  fof(f39,plain,(
% 1.45/0.57    v1_funct_1(sK3)),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f82,plain,(
% 1.45/0.57    spl11_1),
% 1.45/0.57    inference(avatar_split_clause,[],[f37,f79])).
% 1.45/0.57  fof(f37,plain,(
% 1.45/0.57    v1_funct_1(sK4)),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  % SZS output end Proof for theBenchmark
% 1.45/0.57  % (8383)------------------------------
% 1.45/0.57  % (8383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (8383)Termination reason: Refutation
% 1.45/0.57  
% 1.45/0.57  % (8383)Memory used [KB]: 11001
% 1.45/0.57  % (8383)Time elapsed: 0.101 s
% 1.45/0.57  % (8383)------------------------------
% 1.45/0.57  % (8383)------------------------------
% 1.45/0.57  % (8360)Success in time 0.213 s
%------------------------------------------------------------------------------
