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
% DateTime   : Thu Dec  3 13:05:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 155 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  230 ( 706 expanded)
%              Number of equality atoms :   49 ( 168 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f100,f116,f169,f213,f216,f224,f227])).

fof(f227,plain,
    ( ~ spl7_1
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl7_1
    | spl7_9 ),
    inference(resolution,[],[f223,f143])).

fof(f143,plain,
    ( ! [X0] : r2_hidden(sK2,X0)
    | ~ spl7_1 ),
    inference(resolution,[],[f126,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r2_hidden(sK2,X0) )
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f85,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | r2_hidden(sK2,X0) ) ),
    inference(resolution,[],[f54,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
      | r2_hidden(sK2,X0) ) ),
    inference(resolution,[],[f17,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f17,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(f223,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl7_9
  <=> r2_hidden(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f224,plain,
    ( ~ spl7_9
    | spl7_5
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f219,f211,f113,f221])).

fof(f113,plain,
    ( spl7_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f211,plain,
    ( spl7_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | sK3 = X0
        | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f219,plain,
    ( sK2 = sK3
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl7_8 ),
    inference(equality_resolution,[],[f212])).

fof(f212,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f211])).

fof(f216,plain,
    ( ~ spl7_1
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl7_1
    | spl7_7 ),
    inference(resolution,[],[f209,f151])).

fof(f151,plain,
    ( ! [X0] : r2_hidden(sK3,X0)
    | ~ spl7_1 ),
    inference(resolution,[],[f127,f25])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r2_hidden(sK3,X0) )
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f86,f73])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f56,f32])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f18,f31])).

fof(f18,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f209,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK1))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl7_7
  <=> r2_hidden(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f213,plain,
    ( ~ spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f82,f211,f207])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK3 = X0
      | ~ r2_hidden(sK3,k1_relat_1(sK1)) ) ),
    inference(global_subsumption,[],[f21,f24,f60,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | sK3 = X0
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f26,f19])).

fof(f19,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f60,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f169,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f20,f113])).

fof(f20,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f116,plain,
    ( spl7_2
    | spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f105,f97,f113,f75])).

fof(f75,plain,
    ( spl7_2
  <=> sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f97,plain,
    ( spl7_3
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f105,plain,
    ( sK2 = sK3
    | sP6(sK1,sK0)
    | ~ spl7_3 ),
    inference(superposition,[],[f99,f55])).

fof(f55,plain,(
    ! [X1] :
      ( sK2 = k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,sK2))
      | sP6(X1,sK0) ) ),
    inference(resolution,[],[f17,f36])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f36_D])).

fof(f36_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f99,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f100,plain,
    ( spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f92,f97,f75])).

fof(f92,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sP6(sK1,sK0) ),
    inference(superposition,[],[f57,f19])).

fof(f57,plain,(
    ! [X1] :
      ( sK3 = k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,sK3))
      | sP6(X1,sK0) ) ),
    inference(resolution,[],[f18,f36])).

fof(f78,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f59,f75,f71])).

fof(f59,plain,
    ( ~ sP6(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f23,f21,f24,f58])).

fof(f58,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f22,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ sP6(X3,X0) ) ),
    inference(general_splitting,[],[f35,f36_D])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f22,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (24450)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.41  % (24450)Refutation not found, incomplete strategy% (24450)------------------------------
% 0.20/0.41  % (24450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (24450)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (24450)Memory used [KB]: 10618
% 0.20/0.41  % (24450)Time elapsed: 0.004 s
% 0.20/0.41  % (24450)------------------------------
% 0.20/0.41  % (24450)------------------------------
% 0.20/0.46  % (24459)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.46  % (24459)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f228,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f78,f100,f116,f169,f213,f216,f224,f227])).
% 0.20/0.46  fof(f227,plain,(
% 0.20/0.46    ~spl7_1 | spl7_9),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f225])).
% 0.20/0.46  fof(f225,plain,(
% 0.20/0.46    $false | (~spl7_1 | spl7_9)),
% 0.20/0.46    inference(resolution,[],[f223,f143])).
% 0.20/0.46  fof(f143,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK2,X0)) ) | ~spl7_1),
% 0.20/0.46    inference(resolution,[],[f126,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r2_hidden(sK2,X0)) ) | ~spl7_1),
% 0.20/0.46    inference(backward_demodulation,[],[f85,f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    k1_xboole_0 = sK0 | ~spl7_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    spl7_1 <=> k1_xboole_0 = sK0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(sK0,X0) | r2_hidden(sK2,X0)) )),
% 0.20/0.46    inference(resolution,[],[f54,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(sK0,k1_zfmisc_1(X0)) | r2_hidden(sK2,X0)) )),
% 0.20/0.46    inference(resolution,[],[f17,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    r2_hidden(sK2,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 0.20/0.46  fof(f223,plain,(
% 0.20/0.46    ~r2_hidden(sK2,k1_relat_1(sK1)) | spl7_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f221])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    spl7_9 <=> r2_hidden(sK2,k1_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.47  fof(f224,plain,(
% 0.20/0.47    ~spl7_9 | spl7_5 | ~spl7_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f219,f211,f113,f221])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl7_5 <=> sK2 = sK3),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.47  fof(f211,plain,(
% 0.20/0.47    spl7_8 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK3 = X0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    sK2 = sK3 | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~spl7_8),
% 0.20/0.47    inference(equality_resolution,[],[f212])).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl7_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f211])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    ~spl7_1 | spl7_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f214])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    $false | (~spl7_1 | spl7_7)),
% 0.20/0.47    inference(resolution,[],[f209,f151])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK3,X0)) ) | ~spl7_1),
% 0.20/0.47    inference(resolution,[],[f127,f25])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r2_hidden(sK3,X0)) ) | ~spl7_1),
% 0.20/0.47    inference(backward_demodulation,[],[f86,f73])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(sK0,X0) | r2_hidden(sK3,X0)) )),
% 0.20/0.47    inference(resolution,[],[f56,f32])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK0,k1_zfmisc_1(X0)) | r2_hidden(sK3,X0)) )),
% 0.20/0.47    inference(resolution,[],[f18,f31])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    r2_hidden(sK3,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f209,plain,(
% 0.20/0.47    ~r2_hidden(sK3,k1_relat_1(sK1)) | spl7_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f207])).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    spl7_7 <=> r2_hidden(sK3,k1_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    ~spl7_7 | spl7_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f82,f211,f207])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(sK3,k1_relat_1(sK1))) )),
% 0.20/0.47    inference(global_subsumption,[],[f21,f24,f60,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | sK3 = X0 | ~v2_funct_1(sK1)) )),
% 0.20/0.47    inference(superposition,[],[f26,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(resolution,[],[f23,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    v2_funct_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    v1_funct_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    ~spl7_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f113])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    sK2 != sK3),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl7_2 | spl7_5 | ~spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f105,f97,f113,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl7_2 <=> sP6(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl7_3 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    sK2 = sK3 | sP6(sK1,sK0) | ~spl7_3),
% 0.20/0.47    inference(superposition,[],[f99,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X1] : (sK2 = k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,sK2)) | sP6(X1,sK0)) )),
% 0.20/0.47    inference(resolution,[],[f17,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | sP6(X3,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36_D])).
% 0.20/0.47  fof(f36_D,plain,(
% 0.20/0.47    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP6(X3,X0)) )),
% 0.20/0.47    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl7_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl7_2 | spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f92,f97,f75])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sP6(sK1,sK0)),
% 0.20/0.47    inference(superposition,[],[f57,f19])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X1] : (sK3 = k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,sK3)) | sP6(X1,sK0)) )),
% 0.20/0.47    inference(resolution,[],[f18,f36])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl7_1 | ~spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f59,f75,f71])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ~sP6(sK1,sK0) | k1_xboole_0 = sK0),
% 0.20/0.47    inference(global_subsumption,[],[f23,f21,f24,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f22,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | k1_xboole_0 = X1 | ~sP6(X3,X0)) )),
% 0.20/0.47    inference(general_splitting,[],[f35,f36_D])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (24459)------------------------------
% 0.20/0.47  % (24459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (24459)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (24459)Memory used [KB]: 10746
% 0.20/0.47  % (24459)Time elapsed: 0.053 s
% 0.20/0.47  % (24459)------------------------------
% 0.20/0.47  % (24459)------------------------------
% 0.20/0.47  % (24434)Success in time 0.111 s
%------------------------------------------------------------------------------
