%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 168 expanded)
%              Number of leaves         :   26 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  346 ( 630 expanded)
%              Number of equality atoms :   54 (  94 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f585,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f93,f101,f107,f110,f126,f134,f566,f581,f584])).

fof(f584,plain,
    ( ~ spl4_3
    | spl4_1
    | ~ spl4_9
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f583,f579,f99,f64,f72])).

fof(f72,plain,
    ( spl4_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f64,plain,
    ( spl4_1
  <=> r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f99,plain,
    ( spl4_9
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f579,plain,
    ( spl4_87
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r1_tarski(k2_relat_1(sK3),X0)
        | r2_hidden(k1_funct_1(sK3,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f583,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_87 ),
    inference(resolution,[],[f582,f65])).

fof(f65,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f582,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_9
    | ~ spl4_87 ),
    inference(resolution,[],[f580,f100])).

fof(f100,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f580,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | ~ r2_hidden(X1,sK0)
        | r2_hidden(k1_funct_1(sK3,X1),X0) )
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f579])).

fof(f581,plain,
    ( ~ spl4_8
    | spl4_87
    | ~ spl4_13
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f577,f564,f131,f579,f96])).

fof(f96,plain,
    ( spl4_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f131,plain,
    ( spl4_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f564,plain,
    ( spl4_86
  <=> ! [X1,X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f577,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k1_funct_1(sK3,X1),X0)
        | ~ r1_tarski(k2_relat_1(sK3),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_13
    | ~ spl4_86 ),
    inference(forward_demodulation,[],[f575,f132])).

fof(f132,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f575,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X1),X0)
        | ~ r1_tarski(k2_relat_1(sK3),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_86 ),
    inference(superposition,[],[f565,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f565,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X1))))
        | r2_hidden(k1_funct_1(sK3,X0),X1) )
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f564])).

fof(f566,plain,
    ( spl4_86
    | ~ spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f561,f84,f96,f564])).

fof(f84,plain,
    ( spl4_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f561,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X1)))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f414,f85])).

fof(f85,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f414,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(X0,X1),X2)
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,k6_relat_1(X2)))) ) ),
    inference(resolution,[],[f265,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f265,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X0),X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) ) ),
    inference(resolution,[],[f141,f39])).

fof(f39,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f134,plain,
    ( ~ spl4_4
    | spl4_13
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f128,f122,f131,f76])).

fof(f76,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f122,plain,
    ( spl4_12
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f128,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_12 ),
    inference(superposition,[],[f50,f123])).

fof(f123,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f126,plain,
    ( spl4_12
    | spl4_2
    | ~ spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f120,f76,f80,f68,f122])).

fof(f68,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f80,plain,
    ( spl4_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f120,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f52,f77])).

fof(f77,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f110,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f106,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f106,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_10
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f107,plain,
    ( ~ spl4_10
    | ~ spl4_4
    | spl4_8 ),
    inference(avatar_split_clause,[],[f103,f96,f76,f105])).

fof(f103,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_4
    | spl4_8 ),
    inference(resolution,[],[f102,f77])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_8 ),
    inference(resolution,[],[f97,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f97,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f101,plain,
    ( ~ spl4_8
    | spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f94,f91,f99,f96])).

fof(f91,plain,
    ( spl4_7
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f94,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f92,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f89,f76,f91])).

fof(f89,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f51,f77])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f86,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f32,f84])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f82,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f36,f68])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f37,f64])).

fof(f37,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:17:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (1437)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (1436)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (1438)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (1445)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (1444)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (1446)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (1446)Refutation not found, incomplete strategy% (1446)------------------------------
% 0.21/0.51  % (1446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1446)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1446)Memory used [KB]: 6140
% 0.21/0.51  % (1446)Time elapsed: 0.067 s
% 0.21/0.51  % (1446)------------------------------
% 0.21/0.51  % (1446)------------------------------
% 0.21/0.52  % (1451)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (1443)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (1451)Refutation not found, incomplete strategy% (1451)------------------------------
% 0.21/0.52  % (1451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1451)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1451)Memory used [KB]: 10618
% 0.21/0.52  % (1451)Time elapsed: 0.089 s
% 0.21/0.52  % (1451)------------------------------
% 0.21/0.52  % (1451)------------------------------
% 0.21/0.52  % (1443)Refutation not found, incomplete strategy% (1443)------------------------------
% 0.21/0.52  % (1443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1443)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1443)Memory used [KB]: 6140
% 0.21/0.52  % (1443)Time elapsed: 0.090 s
% 0.21/0.52  % (1443)------------------------------
% 0.21/0.52  % (1443)------------------------------
% 0.21/0.52  % (1437)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f585,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f93,f101,f107,f110,f126,f134,f566,f581,f584])).
% 0.21/0.52  fof(f584,plain,(
% 0.21/0.52    ~spl4_3 | spl4_1 | ~spl4_9 | ~spl4_87),
% 0.21/0.52    inference(avatar_split_clause,[],[f583,f579,f99,f64,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl4_3 <=> r2_hidden(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl4_1 <=> r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl4_9 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f579,plain,(
% 0.21/0.52    spl4_87 <=> ! [X1,X0] : (~r2_hidden(X1,sK0) | ~r1_tarski(k2_relat_1(sK3),X0) | r2_hidden(k1_funct_1(sK3,X1),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 0.21/0.52  fof(f583,plain,(
% 0.21/0.52    ~r2_hidden(sK2,sK0) | (spl4_1 | ~spl4_9 | ~spl4_87)),
% 0.21/0.52    inference(resolution,[],[f582,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f64])).
% 0.21/0.52  fof(f582,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK1) | ~r2_hidden(X0,sK0)) ) | (~spl4_9 | ~spl4_87)),
% 0.21/0.52    inference(resolution,[],[f580,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK3),sK1) | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f99])).
% 0.21/0.52  fof(f580,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),X0) | ~r2_hidden(X1,sK0) | r2_hidden(k1_funct_1(sK3,X1),X0)) ) | ~spl4_87),
% 0.21/0.52    inference(avatar_component_clause,[],[f579])).
% 0.21/0.52  fof(f581,plain,(
% 0.21/0.52    ~spl4_8 | spl4_87 | ~spl4_13 | ~spl4_86),
% 0.21/0.52    inference(avatar_split_clause,[],[f577,f564,f131,f579,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl4_8 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl4_13 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.52  fof(f564,plain,(
% 0.21/0.52    spl4_86 <=> ! [X1,X0] : (r2_hidden(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X1)))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 0.21/0.52  fof(f577,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | r2_hidden(k1_funct_1(sK3,X1),X0) | ~r1_tarski(k2_relat_1(sK3),X0) | ~v1_relat_1(sK3)) ) | (~spl4_13 | ~spl4_86)),
% 0.21/0.52    inference(forward_demodulation,[],[f575,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK3) | ~spl4_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f575,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X1),X0) | ~r1_tarski(k2_relat_1(sK3),X0) | ~v1_relat_1(sK3)) ) | ~spl4_86),
% 0.21/0.52    inference(superposition,[],[f565,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.52  fof(f565,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X1)))) | r2_hidden(k1_funct_1(sK3,X0),X1)) ) | ~spl4_86),
% 0.21/0.52    inference(avatar_component_clause,[],[f564])).
% 0.21/0.52  fof(f566,plain,(
% 0.21/0.52    spl4_86 | ~spl4_8 | ~spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f561,f84,f96,f564])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl4_6 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f561,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,k6_relat_1(X1))))) ) | ~spl4_6),
% 0.21/0.52    inference(resolution,[],[f414,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    v1_funct_1(sK3) | ~spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f84])).
% 0.21/0.52  fof(f414,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(k1_funct_1(X0,X1),X2) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,k6_relat_1(X2))))) )),
% 0.21/0.52    inference(resolution,[],[f265,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.52  fof(f265,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(k6_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))) )),
% 0.21/0.52    inference(resolution,[],[f141,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(k6_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.52    inference(superposition,[],[f48,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~spl4_4 | spl4_13 | ~spl4_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f128,f122,f131,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl4_12 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_12),
% 0.21/0.52    inference(superposition,[],[f50,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl4_12 | spl4_2 | ~spl4_5 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f120,f76,f80,f68,f122])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl4_2 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl4_5 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f52,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl4_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    $false | spl4_10),
% 0.21/0.52    inference(resolution,[],[f106,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl4_10 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ~spl4_10 | ~spl4_4 | spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f103,f96,f76,f105])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl4_4 | spl4_8)),
% 0.21/0.52    inference(resolution,[],[f102,f77])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_8),
% 0.21/0.52    inference(resolution,[],[f97,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~spl4_8 | spl4_9 | ~spl4_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f94,f91,f99,f96])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl4_7 <=> v5_relat_1(sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl4_7),
% 0.21/0.52    inference(resolution,[],[f92,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    v5_relat_1(sK3,sK1) | ~spl4_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl4_7 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f89,f76,f91])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    v5_relat_1(sK3,sK1) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f51,f77])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f84])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK3,sK2),sK1) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f80])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f76])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f72])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    r2_hidden(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f68])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f37,f64])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (1437)------------------------------
% 0.21/0.52  % (1437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1437)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (1437)Memory used [KB]: 11129
% 0.21/0.52  % (1437)Time elapsed: 0.075 s
% 0.21/0.52  % (1437)------------------------------
% 0.21/0.52  % (1437)------------------------------
% 0.21/0.52  % (1430)Success in time 0.158 s
%------------------------------------------------------------------------------
