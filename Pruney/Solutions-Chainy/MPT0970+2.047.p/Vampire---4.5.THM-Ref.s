%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:55 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 332 expanded)
%              Number of leaves         :   18 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  226 (1236 expanded)
%              Number of equality atoms :   49 ( 292 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f119,f142,f152,f156,f177,f214])).

fof(f214,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f50,f196])).

fof(f196,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f99,f110])).

fof(f110,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f99,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f85,f93,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f93,plain,(
    ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f50,f86,f37])).

fof(f86,plain,(
    ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f83,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f75,f81,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f81,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f31,f64])).

fof(f64,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f30,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f31,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f65,f62,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f62,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f30,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f65,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f41,f30,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f85,plain,(
    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f83,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f177,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f85,f88,f86,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK3(X0),sK0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_6
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f88,plain,(
    r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f85,f26])).

fof(f26,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f156,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f28,f138])).

fof(f138,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f152,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f41,f30,f134,f40])).

fof(f134,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f142,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f120,f112,f140,f136,f132])).

fof(f112,plain,
    ( spl5_3
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f84,f114])).

fof(f114,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f84,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f36,f27])).

fof(f27,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f119,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f29,f106])).

fof(f106,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_1
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f29,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,
    ( ~ spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f72,f112,f108,f104])).

fof(f72,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f70,f63])).

fof(f63,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f30,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f30,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (5263)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (5237)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (5242)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (5239)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (5235)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (5247)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (5236)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.52  % (5246)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.21/0.52  % (5245)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.21/0.52  % (5258)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.21/0.52  % (5250)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.21/0.52  % (5257)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.53  % (5260)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.21/0.53  % (5264)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.21/0.53  % (5238)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.53  % (5249)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.21/0.53  % (5240)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.53  % (5239)Refutation found. Thanks to Tanya!
% 1.21/0.53  % SZS status Theorem for theBenchmark
% 1.21/0.53  % SZS output start Proof for theBenchmark
% 1.21/0.53  fof(f215,plain,(
% 1.21/0.53    $false),
% 1.21/0.53    inference(avatar_sat_refutation,[],[f115,f119,f142,f152,f156,f177,f214])).
% 1.21/0.53  fof(f214,plain,(
% 1.21/0.53    ~spl5_2),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f205])).
% 1.21/0.53  fof(f205,plain,(
% 1.21/0.53    $false | ~spl5_2),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f50,f196])).
% 1.21/0.53  fof(f196,plain,(
% 1.21/0.53    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl5_2),
% 1.21/0.53    inference(backward_demodulation,[],[f99,f110])).
% 1.21/0.53  fof(f110,plain,(
% 1.21/0.53    k1_xboole_0 = sK1 | ~spl5_2),
% 1.21/0.53    inference(avatar_component_clause,[],[f108])).
% 1.21/0.53  fof(f108,plain,(
% 1.21/0.53    spl5_2 <=> k1_xboole_0 = sK1),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.21/0.53  fof(f99,plain,(
% 1.21/0.53    ~r1_tarski(sK1,k1_xboole_0)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f85,f93,f37])).
% 1.21/0.53  fof(f37,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f19])).
% 1.21/0.53  fof(f19,plain,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.21/0.53    inference(ennf_transformation,[],[f1])).
% 1.21/0.53  fof(f1,axiom,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.21/0.53  fof(f93,plain,(
% 1.21/0.53    ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),k1_xboole_0)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f50,f86,f37])).
% 1.21/0.53  fof(f86,plain,(
% 1.21/0.53    ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f83,f39])).
% 1.21/0.53  fof(f39,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f19])).
% 1.21/0.53  fof(f83,plain,(
% 1.21/0.53    ~r1_tarski(sK1,k2_relat_1(sK2))),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f75,f81,f35])).
% 1.21/0.53  fof(f35,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.21/0.53    inference(cnf_transformation,[],[f2])).
% 1.21/0.53  fof(f2,axiom,(
% 1.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.21/0.53  fof(f81,plain,(
% 1.21/0.53    sK1 != k2_relat_1(sK2)),
% 1.21/0.53    inference(superposition,[],[f31,f64])).
% 1.21/0.53  fof(f64,plain,(
% 1.21/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f30,f32])).
% 1.21/0.53  fof(f32,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f16])).
% 1.21/0.53  fof(f16,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(ennf_transformation,[],[f10])).
% 1.21/0.53  fof(f10,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.21/0.53  fof(f30,plain,(
% 1.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f15,plain,(
% 1.21/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.21/0.53    inference(flattening,[],[f14])).
% 1.21/0.53  fof(f14,plain,(
% 1.21/0.53    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.21/0.53    inference(ennf_transformation,[],[f13])).
% 1.21/0.53  fof(f13,negated_conjecture,(
% 1.21/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.21/0.53    inference(negated_conjecture,[],[f12])).
% 1.21/0.53  fof(f12,conjecture,(
% 1.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 1.21/0.53  fof(f31,plain,(
% 1.21/0.53    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f75,plain,(
% 1.21/0.53    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f65,f62,f49])).
% 1.21/0.53  fof(f49,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f23])).
% 1.21/0.53  fof(f23,plain,(
% 1.21/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f5])).
% 1.21/0.53  fof(f5,axiom,(
% 1.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.21/0.53  fof(f62,plain,(
% 1.21/0.53    v5_relat_1(sK2,sK1)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f30,f53])).
% 1.21/0.53  fof(f53,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f25])).
% 1.21/0.53  fof(f25,plain,(
% 1.21/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(ennf_transformation,[],[f8])).
% 1.21/0.53  fof(f8,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.21/0.53  fof(f65,plain,(
% 1.21/0.53    v1_relat_1(sK2)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f41,f30,f40])).
% 1.21/0.53  fof(f40,plain,(
% 1.21/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  fof(f20,plain,(
% 1.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.21/0.53    inference(ennf_transformation,[],[f4])).
% 1.21/0.53  fof(f4,axiom,(
% 1.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.21/0.53  fof(f41,plain,(
% 1.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f6])).
% 1.21/0.53  fof(f6,axiom,(
% 1.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.21/0.53  fof(f85,plain,(
% 1.21/0.53    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f83,f38])).
% 1.21/0.53  fof(f38,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f19])).
% 1.21/0.53  fof(f50,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f3])).
% 1.21/0.53  fof(f3,axiom,(
% 1.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.21/0.53  fof(f177,plain,(
% 1.21/0.53    ~spl5_6),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f174])).
% 1.21/0.53  fof(f174,plain,(
% 1.21/0.53    $false | ~spl5_6),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f85,f88,f86,f141])).
% 1.21/0.53  fof(f141,plain,(
% 1.21/0.53    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK3(X0),sK0)) ) | ~spl5_6),
% 1.21/0.53    inference(avatar_component_clause,[],[f140])).
% 1.21/0.53  fof(f140,plain,(
% 1.21/0.53    spl5_6 <=> ! [X0] : (~r2_hidden(sK3(X0),sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X0,k2_relat_1(sK2)))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.21/0.53  fof(f88,plain,(
% 1.21/0.53    r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f85,f26])).
% 1.21/0.53  fof(f26,plain,(
% 1.21/0.53    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f156,plain,(
% 1.21/0.53    spl5_5),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f153])).
% 1.21/0.53  fof(f153,plain,(
% 1.21/0.53    $false | spl5_5),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f28,f138])).
% 1.21/0.53  fof(f138,plain,(
% 1.21/0.53    ~v1_funct_1(sK2) | spl5_5),
% 1.21/0.53    inference(avatar_component_clause,[],[f136])).
% 1.21/0.53  fof(f136,plain,(
% 1.21/0.53    spl5_5 <=> v1_funct_1(sK2)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.21/0.53  fof(f28,plain,(
% 1.21/0.53    v1_funct_1(sK2)),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f152,plain,(
% 1.21/0.53    spl5_4),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f147])).
% 1.21/0.53  fof(f147,plain,(
% 1.21/0.53    $false | spl5_4),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f41,f30,f134,f40])).
% 1.21/0.53  fof(f134,plain,(
% 1.21/0.53    ~v1_relat_1(sK2) | spl5_4),
% 1.21/0.53    inference(avatar_component_clause,[],[f132])).
% 1.21/0.53  fof(f132,plain,(
% 1.21/0.53    spl5_4 <=> v1_relat_1(sK2)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.21/0.53  fof(f142,plain,(
% 1.21/0.53    ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_3),
% 1.21/0.53    inference(avatar_split_clause,[],[f120,f112,f140,f136,f132])).
% 1.21/0.53  fof(f112,plain,(
% 1.21/0.53    spl5_3 <=> sK0 = k1_relat_1(sK2)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.21/0.53  fof(f120,plain,(
% 1.21/0.53    ( ! [X0] : (~r2_hidden(sK3(X0),sK0) | r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X0,sK1)) ) | ~spl5_3),
% 1.21/0.53    inference(backward_demodulation,[],[f84,f114])).
% 1.21/0.53  fof(f114,plain,(
% 1.21/0.53    sK0 = k1_relat_1(sK2) | ~spl5_3),
% 1.21/0.53    inference(avatar_component_clause,[],[f112])).
% 1.21/0.53  fof(f84,plain,(
% 1.21/0.53    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(X0),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X0,sK1)) )),
% 1.21/0.53    inference(superposition,[],[f36,f27])).
% 1.21/0.53  fof(f27,plain,(
% 1.21/0.53    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f36,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f18])).
% 1.21/0.53  fof(f18,plain,(
% 1.21/0.53    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.21/0.53    inference(flattening,[],[f17])).
% 1.21/0.53  fof(f17,plain,(
% 1.21/0.53    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.21/0.53    inference(ennf_transformation,[],[f7])).
% 1.21/0.53  fof(f7,axiom,(
% 1.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 1.21/0.53  fof(f119,plain,(
% 1.21/0.53    spl5_1),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f116])).
% 1.21/0.53  fof(f116,plain,(
% 1.21/0.53    $false | spl5_1),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f29,f106])).
% 1.21/0.53  fof(f106,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,sK0,sK1) | spl5_1),
% 1.21/0.53    inference(avatar_component_clause,[],[f104])).
% 1.21/0.53  fof(f104,plain,(
% 1.21/0.53    spl5_1 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.21/0.53  fof(f29,plain,(
% 1.21/0.53    v1_funct_2(sK2,sK0,sK1)),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f115,plain,(
% 1.21/0.53    ~spl5_1 | spl5_2 | spl5_3),
% 1.21/0.53    inference(avatar_split_clause,[],[f72,f112,f108,f104])).
% 1.21/0.53  fof(f72,plain,(
% 1.21/0.53    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 1.21/0.53    inference(forward_demodulation,[],[f70,f63])).
% 1.21/0.53  fof(f63,plain,(
% 1.21/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f30,f51])).
% 1.21/0.53  fof(f51,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f24])).
% 1.21/0.53  fof(f24,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(ennf_transformation,[],[f9])).
% 1.21/0.53  fof(f9,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.21/0.53  fof(f70,plain,(
% 1.21/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.21/0.53    inference(resolution,[],[f30,f47])).
% 1.21/0.53  fof(f47,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f22])).
% 1.21/0.53  fof(f22,plain,(
% 1.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(flattening,[],[f21])).
% 1.21/0.53  fof(f21,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(ennf_transformation,[],[f11])).
% 1.21/0.53  fof(f11,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.21/0.53  % SZS output end Proof for theBenchmark
% 1.21/0.53  % (5239)------------------------------
% 1.21/0.53  % (5239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (5239)Termination reason: Refutation
% 1.21/0.53  
% 1.21/0.53  % (5239)Memory used [KB]: 6268
% 1.21/0.53  % (5239)Time elapsed: 0.132 s
% 1.21/0.53  % (5239)------------------------------
% 1.21/0.53  % (5239)------------------------------
% 1.21/0.53  % (5244)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.21/0.53  % (5234)Success in time 0.174 s
%------------------------------------------------------------------------------
