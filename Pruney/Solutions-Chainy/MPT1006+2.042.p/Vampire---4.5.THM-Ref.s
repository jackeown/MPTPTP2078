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
% DateTime   : Thu Dec  3 13:03:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 100 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  186 ( 272 expanded)
%              Number of equality atoms :   32 (  55 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f66,f70,f74,f83,f94,f98,f121,f136,f141])).

fof(f141,plain,
    ( ~ spl4_6
    | spl4_19
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl4_6
    | spl4_19
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f57,f120,f135])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X0,X2) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_22
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f120,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_19
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f57,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_6
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f136,plain,
    ( spl4_22
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f123,f96,f92,f64,f134])).

fof(f64,plain,
    ( spl4_8
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f92,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f96,plain,
    ( spl4_15
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X0,X2) )
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f122,f65])).

fof(f65,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X0,X2) )
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(resolution,[],[f97,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f97,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f121,plain,
    ( ~ spl4_19
    | ~ spl4_3
    | spl4_5
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f102,f92,f52,f44,f119])).

fof(f44,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f52,plain,
    ( spl4_5
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f102,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f53,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(resolution,[],[f93,f45])).

fof(f45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f53,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f98,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f31,f96])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f94,plain,
    ( spl4_14
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f88,f81,f68,f92])).

fof(f68,plain,
    ( spl4_9
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK3(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f81,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(resolution,[],[f82,f69])).

fof(f69,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f79,f72,f48,f81])).

fof(f48,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f72,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f70,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f66,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f58,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f54,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(f50,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f46,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f44])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f20,f33])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (19662)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.41  % (19662)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f143,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f66,f70,f74,f83,f94,f98,f121,f136,f141])).
% 0.20/0.41  fof(f141,plain,(
% 0.20/0.41    ~spl4_6 | spl4_19 | ~spl4_22),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.41  fof(f137,plain,(
% 0.20/0.41    $false | (~spl4_6 | spl4_19 | ~spl4_22)),
% 0.20/0.41    inference(unit_resulting_resolution,[],[f57,f120,f135])).
% 0.20/0.41  fof(f135,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X0,X2)) ) | ~spl4_22),
% 0.20/0.41    inference(avatar_component_clause,[],[f134])).
% 0.20/0.41  fof(f134,plain,(
% 0.20/0.41    spl4_22 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X0,X2))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.41  fof(f120,plain,(
% 0.20/0.41    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl4_19),
% 0.20/0.41    inference(avatar_component_clause,[],[f119])).
% 0.20/0.41  fof(f119,plain,(
% 0.20/0.41    spl4_19 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl4_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f56])).
% 0.20/0.41  fof(f56,plain,(
% 0.20/0.41    spl4_6 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.41  fof(f136,plain,(
% 0.20/0.41    spl4_22 | ~spl4_8 | ~spl4_14 | ~spl4_15),
% 0.20/0.41    inference(avatar_split_clause,[],[f123,f96,f92,f64,f134])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    spl4_8 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.41  fof(f92,plain,(
% 0.20/0.41    spl4_14 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.41  fof(f96,plain,(
% 0.20/0.41    spl4_15 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.41  fof(f123,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X0,X2)) ) | (~spl4_8 | ~spl4_14 | ~spl4_15)),
% 0.20/0.41    inference(forward_demodulation,[],[f122,f65])).
% 0.20/0.41  fof(f65,plain,(
% 0.20/0.41    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl4_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f64])).
% 0.20/0.41  fof(f122,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X0,X2)) ) | (~spl4_14 | ~spl4_15)),
% 0.20/0.41    inference(resolution,[],[f97,f93])).
% 0.20/0.41  fof(f93,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_14),
% 0.20/0.41    inference(avatar_component_clause,[],[f92])).
% 0.20/0.41  fof(f97,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_15),
% 0.20/0.41    inference(avatar_component_clause,[],[f96])).
% 0.20/0.41  fof(f121,plain,(
% 0.20/0.41    ~spl4_19 | ~spl4_3 | spl4_5 | ~spl4_14),
% 0.20/0.41    inference(avatar_split_clause,[],[f102,f92,f52,f44,f119])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    spl4_5 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.41  fof(f102,plain,(
% 0.20/0.41    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (~spl4_3 | spl4_5 | ~spl4_14)),
% 0.20/0.41    inference(backward_demodulation,[],[f53,f99])).
% 0.20/0.41  fof(f99,plain,(
% 0.20/0.41    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_14)),
% 0.20/0.41    inference(resolution,[],[f93,f45])).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f44])).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f52])).
% 0.20/0.41  fof(f98,plain,(
% 0.20/0.41    spl4_15),
% 0.20/0.41    inference(avatar_split_clause,[],[f31,f96])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.20/0.41  fof(f94,plain,(
% 0.20/0.41    spl4_14 | ~spl4_9 | ~spl4_12),
% 0.20/0.41    inference(avatar_split_clause,[],[f88,f81,f68,f92])).
% 0.20/0.41  fof(f68,plain,(
% 0.20/0.41    spl4_9 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.41  fof(f81,plain,(
% 0.20/0.41    spl4_12 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.41  fof(f88,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl4_9 | ~spl4_12)),
% 0.20/0.41    inference(resolution,[],[f82,f69])).
% 0.20/0.41  fof(f69,plain,(
% 0.20/0.41    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_9),
% 0.20/0.41    inference(avatar_component_clause,[],[f68])).
% 0.20/0.41  fof(f82,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_12),
% 0.20/0.41    inference(avatar_component_clause,[],[f81])).
% 0.20/0.41  fof(f83,plain,(
% 0.20/0.41    spl4_12 | ~spl4_4 | ~spl4_10),
% 0.20/0.41    inference(avatar_split_clause,[],[f79,f72,f48,f81])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    spl4_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.41  fof(f72,plain,(
% 0.20/0.41    spl4_10 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.41  fof(f79,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | (~spl4_4 | ~spl4_10)),
% 0.20/0.41    inference(resolution,[],[f73,f49])).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    v1_xboole_0(k1_xboole_0) | ~spl4_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f48])).
% 0.20/0.41  fof(f73,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl4_10),
% 0.20/0.41    inference(avatar_component_clause,[],[f72])).
% 0.20/0.41  fof(f74,plain,(
% 0.20/0.41    spl4_10),
% 0.20/0.41    inference(avatar_split_clause,[],[f30,f72])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    spl4_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f25,f68])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.41    inference(flattening,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.41    inference(ennf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,axiom,(
% 0.20/0.41    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    spl4_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f33,f64])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.41    inference(equality_resolution,[],[f27])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.41  fof(f58,plain,(
% 0.20/0.41    spl4_6),
% 0.20/0.41    inference(avatar_split_clause,[],[f23,f56])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ~spl4_5),
% 0.20/0.41    inference(avatar_split_clause,[],[f21,f52])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.20/0.41    inference(flattening,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.41    inference(negated_conjecture,[],[f8])).
% 0.20/0.41  fof(f8,conjecture,(
% 0.20/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    spl4_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f22,f48])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    v1_xboole_0(k1_xboole_0)),
% 0.20/0.41    inference(cnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    v1_xboole_0(k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.41  fof(f46,plain,(
% 0.20/0.41    spl4_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f34,f44])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.41    inference(backward_demodulation,[],[f20,f33])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (19662)------------------------------
% 0.20/0.41  % (19662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (19662)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (19662)Memory used [KB]: 10618
% 0.20/0.41  % (19662)Time elapsed: 0.007 s
% 0.20/0.41  % (19662)------------------------------
% 0.20/0.41  % (19662)------------------------------
% 0.20/0.42  % (19652)Success in time 0.058 s
%------------------------------------------------------------------------------
