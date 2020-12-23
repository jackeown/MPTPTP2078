%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 200 expanded)
%              Number of leaves         :   26 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  350 ( 585 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f560,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f73,f78,f98,f130,f136,f159,f169,f181,f257,f283,f516,f553,f559])).

fof(f559,plain,
    ( spl7_24
    | spl7_53
    | ~ spl7_58 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | spl7_24
    | spl7_53
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f557,f282])).

fof(f282,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl7_24
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f557,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | spl7_53
    | ~ spl7_58 ),
    inference(resolution,[],[f552,f519])).

fof(f519,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r2_hidden(X0,sK0) )
    | spl7_53 ),
    inference(resolution,[],[f515,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f515,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_53 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl7_53
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f552,plain,
    ( m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl7_58
  <=> m1_subset_1(sK6(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f553,plain,
    ( spl7_58
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f510,f156,f121,f70,f550])).

fof(f70,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f121,plain,
    ( spl7_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f156,plain,
    ( spl7_14
  <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f510,plain,
    ( m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(resolution,[],[f361,f72])).

fof(f72,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f361,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(sK6(sK4,sK2,sK3),X0) )
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(resolution,[],[f296,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f296,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | m1_subset_1(sK6(sK4,sK2,sK3),X0) )
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f295,f122])).

fof(f122,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f295,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(sK4,sK2,sK3),X0)
        | ~ v1_relat_1(sK3)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl7_14 ),
    inference(resolution,[],[f266,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f266,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK3),X0)
        | m1_subset_1(sK6(sK4,sK2,sK3),X0) )
    | ~ spl7_14 ),
    inference(resolution,[],[f162,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f162,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X2))
        | m1_subset_1(sK6(sK4,sK2,sK3),X2) )
    | ~ spl7_14 ),
    inference(resolution,[],[f158,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f158,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f516,plain,
    ( ~ spl7_53
    | ~ spl7_3
    | ~ spl7_10
    | spl7_15 ),
    inference(avatar_split_clause,[],[f508,f166,f121,f70,f513])).

fof(f166,plain,
    ( spl7_15
  <=> v1_xboole_0(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f508,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl7_3
    | ~ spl7_10
    | spl7_15 ),
    inference(resolution,[],[f272,f72])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl7_10
    | spl7_15 ),
    inference(resolution,[],[f269,f48])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_10
    | spl7_15 ),
    inference(subsumption_resolution,[],[f268,f122])).

% (26535)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f268,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(sK3)
        | ~ v4_relat_1(sK3,X0) )
    | spl7_15 ),
    inference(resolution,[],[f267,f40])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK3),X0)
        | ~ v1_xboole_0(X0) )
    | spl7_15 ),
    inference(resolution,[],[f173,f42])).

fof(f173,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | spl7_15 ),
    inference(resolution,[],[f168,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f168,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f283,plain,
    ( ~ spl7_24
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f260,f254,f133,f280])).

fof(f133,plain,
    ( spl7_11
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f254,plain,
    ( spl7_23
  <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f260,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f259,f135])).

fof(f135,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f259,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_23 ),
    inference(trivial_inequality_removal,[],[f258])).

fof(f258,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ r2_hidden(sK6(sK4,sK2,sK3),sK0)
    | ~ spl7_23 ),
    inference(superposition,[],[f29,f256])).

fof(f256,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f254])).

fof(f29,plain,(
    ! [X5] :
      ( sK4 != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f257,plain,
    ( spl7_23
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f183,f178,f121,f57,f254])).

fof(f57,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f178,plain,
    ( spl7_16
  <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f183,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_16 ),
    inference(resolution,[],[f180,f137])).

fof(f137,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | k1_funct_1(sK3,X2) = X3 )
    | ~ spl7_1
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f62,f122])).

fof(f62,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK3) )
    | ~ spl7_1 ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f59,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f180,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f181,plain,
    ( spl7_16
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f174,f121,f95,f178])).

fof(f95,plain,
    ( spl7_7
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f174,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f100,f122])).

fof(f100,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f97,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f97,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f169,plain,
    ( ~ spl7_15
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f163,f156,f166])).

fof(f163,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | ~ spl7_14 ),
    inference(resolution,[],[f158,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f159,plain,
    ( spl7_14
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f149,f121,f95,f156])).

fof(f149,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f99,f122])).

fof(f99,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f136,plain,
    ( spl7_11
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f131,f121,f95,f133])).

fof(f131,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f101,f122])).

fof(f101,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f97,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f130,plain,
    ( ~ spl7_3
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl7_3
    | spl7_10 ),
    inference(subsumption_resolution,[],[f127,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f127,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_3
    | spl7_10 ),
    inference(resolution,[],[f125,f72])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_10 ),
    inference(resolution,[],[f123,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f123,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f98,plain,
    ( spl7_7
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f88,f75,f70,f95])).

fof(f75,plain,
    ( spl7_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f88,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f87,f72])).

fof(f87,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(superposition,[],[f77,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f77,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f78,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f33,f70])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (26536)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (26544)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (26546)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (26554)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (26546)Refutation not found, incomplete strategy% (26546)------------------------------
% 0.22/0.48  % (26546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26546)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26546)Memory used [KB]: 1663
% 0.22/0.48  % (26546)Time elapsed: 0.062 s
% 0.22/0.48  % (26546)------------------------------
% 0.22/0.48  % (26546)------------------------------
% 0.22/0.48  % (26536)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (26538)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (26552)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (26547)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (26539)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (26554)Refutation not found, incomplete strategy% (26554)------------------------------
% 0.22/0.50  % (26554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26554)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26554)Memory used [KB]: 10618
% 0.22/0.50  % (26554)Time elapsed: 0.078 s
% 0.22/0.50  % (26554)------------------------------
% 0.22/0.50  % (26554)------------------------------
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f560,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f60,f73,f78,f98,f130,f136,f159,f169,f181,f257,f283,f516,f553,f559])).
% 0.22/0.50  fof(f559,plain,(
% 0.22/0.50    spl7_24 | spl7_53 | ~spl7_58),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f558])).
% 0.22/0.50  fof(f558,plain,(
% 0.22/0.50    $false | (spl7_24 | spl7_53 | ~spl7_58)),
% 0.22/0.50    inference(subsumption_resolution,[],[f557,f282])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | spl7_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f280])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    spl7_24 <=> r2_hidden(sK6(sK4,sK2,sK3),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.50  fof(f557,plain,(
% 0.22/0.50    r2_hidden(sK6(sK4,sK2,sK3),sK0) | (spl7_53 | ~spl7_58)),
% 0.22/0.50    inference(resolution,[],[f552,f519])).
% 0.22/0.50  fof(f519,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,sK0) | r2_hidden(X0,sK0)) ) | spl7_53),
% 0.22/0.50    inference(resolution,[],[f515,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f515,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0) | spl7_53),
% 0.22/0.50    inference(avatar_component_clause,[],[f513])).
% 0.22/0.50  fof(f513,plain,(
% 0.22/0.50    spl7_53 <=> v1_xboole_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 0.22/0.50  fof(f552,plain,(
% 0.22/0.50    m1_subset_1(sK6(sK4,sK2,sK3),sK0) | ~spl7_58),
% 0.22/0.50    inference(avatar_component_clause,[],[f550])).
% 0.22/0.50  fof(f550,plain,(
% 0.22/0.50    spl7_58 <=> m1_subset_1(sK6(sK4,sK2,sK3),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 0.22/0.50  fof(f553,plain,(
% 0.22/0.50    spl7_58 | ~spl7_3 | ~spl7_10 | ~spl7_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f510,f156,f121,f70,f550])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl7_10 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl7_14 <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.50  fof(f510,plain,(
% 0.22/0.50    m1_subset_1(sK6(sK4,sK2,sK3),sK0) | (~spl7_3 | ~spl7_10 | ~spl7_14)),
% 0.22/0.50    inference(resolution,[],[f361,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f70])).
% 0.22/0.50  fof(f361,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(sK6(sK4,sK2,sK3),X0)) ) | (~spl7_10 | ~spl7_14)),
% 0.22/0.50    inference(resolution,[],[f296,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0) | m1_subset_1(sK6(sK4,sK2,sK3),X0)) ) | (~spl7_10 | ~spl7_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f295,f122])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    v1_relat_1(sK3) | ~spl7_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(sK6(sK4,sK2,sK3),X0) | ~v1_relat_1(sK3) | ~v4_relat_1(sK3,X0)) ) | ~spl7_14),
% 0.22/0.50    inference(resolution,[],[f266,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(sK6(sK4,sK2,sK3),X0)) ) | ~spl7_14),
% 0.22/0.50    inference(resolution,[],[f162,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X2)) | m1_subset_1(sK6(sK4,sK2,sK3),X2)) ) | ~spl7_14),
% 0.22/0.50    inference(resolution,[],[f158,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl7_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f156])).
% 0.22/0.50  fof(f516,plain,(
% 0.22/0.50    ~spl7_53 | ~spl7_3 | ~spl7_10 | spl7_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f508,f166,f121,f70,f513])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    spl7_15 <=> v1_xboole_0(k1_relat_1(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.50  fof(f508,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0) | (~spl7_3 | ~spl7_10 | spl7_15)),
% 0.22/0.50    inference(resolution,[],[f272,f72])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) ) | (~spl7_10 | spl7_15)),
% 0.22/0.50    inference(resolution,[],[f269,f48])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_xboole_0(X0)) ) | (~spl7_10 | spl7_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f268,f122])).
% 0.22/0.50  % (26535)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_relat_1(sK3) | ~v4_relat_1(sK3,X0)) ) | spl7_15),
% 0.22/0.50    inference(resolution,[],[f267,f40])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | ~v1_xboole_0(X0)) ) | spl7_15),
% 0.22/0.50    inference(resolution,[],[f173,f42])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) ) | spl7_15),
% 0.22/0.50    inference(resolution,[],[f168,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_relat_1(sK3)) | spl7_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f166])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    ~spl7_24 | ~spl7_11 | ~spl7_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f260,f254,f133,f280])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl7_11 <=> r2_hidden(sK6(sK4,sK2,sK3),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    spl7_23 <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | (~spl7_11 | ~spl7_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f259,f135])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~spl7_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    ~r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | ~spl7_23),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f258])).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    sK4 != sK4 | ~r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~r2_hidden(sK6(sK4,sK2,sK3),sK0) | ~spl7_23),
% 0.22/0.50    inference(superposition,[],[f29,f256])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~spl7_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f254])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    spl7_23 | ~spl7_1 | ~spl7_10 | ~spl7_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f183,f178,f121,f57,f254])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl7_1 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    spl7_16 <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | (~spl7_1 | ~spl7_10 | ~spl7_16)),
% 0.22/0.50    inference(resolution,[],[f180,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | k1_funct_1(sK3,X2) = X3) ) | (~spl7_1 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f62,f122])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~v1_relat_1(sK3) | k1_funct_1(sK3,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK3)) ) | ~spl7_1),
% 0.22/0.50    inference(resolution,[],[f59,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    v1_funct_1(sK3) | ~spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~spl7_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f178])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    spl7_16 | ~spl7_7 | ~spl7_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f174,f121,f95,f178])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl7_7 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | (~spl7_7 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f100,f122])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl7_7),
% 0.22/0.50    inference(resolution,[],[f97,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl7_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ~spl7_15 | ~spl7_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f163,f156,f166])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_relat_1(sK3)) | ~spl7_14),
% 0.22/0.50    inference(resolution,[],[f158,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    spl7_14 | ~spl7_7 | ~spl7_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f149,f121,f95,f156])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl7_7 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f99,f122])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl7_7),
% 0.22/0.50    inference(resolution,[],[f97,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl7_11 | ~spl7_7 | ~spl7_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f131,f121,f95,f133])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    r2_hidden(sK6(sK4,sK2,sK3),sK2) | (~spl7_7 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f101,f122])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl7_7),
% 0.22/0.50    inference(resolution,[],[f97,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ~spl7_3 | spl7_10),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f129])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    $false | (~spl7_3 | spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f127,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_3 | spl7_10)),
% 0.22/0.50    inference(resolution,[],[f125,f72])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_10),
% 0.22/0.50    inference(resolution,[],[f123,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ~v1_relat_1(sK3) | spl7_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl7_7 | ~spl7_3 | ~spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f88,f75,f70,f95])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl7_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl7_3 | ~spl7_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f87,f72])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_4),
% 0.22/0.50    inference(superposition,[],[f77,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl7_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f75])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f75])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl7_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f70])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl7_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f57])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (26536)------------------------------
% 0.22/0.50  % (26536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26536)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (26536)Memory used [KB]: 11001
% 0.22/0.50  % (26536)Time elapsed: 0.071 s
% 0.22/0.50  % (26536)------------------------------
% 0.22/0.50  % (26536)------------------------------
% 0.22/0.50  % (26529)Success in time 0.141 s
%------------------------------------------------------------------------------
