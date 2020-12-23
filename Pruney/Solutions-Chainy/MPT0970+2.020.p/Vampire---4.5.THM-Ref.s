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
% DateTime   : Thu Dec  3 13:00:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 188 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  217 ( 677 expanded)
%              Number of equality atoms :   31 ( 158 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f131,f135,f142,f146,f165,f247,f318])).

fof(f318,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f71,f84])).

fof(f84,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_1
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f29,f47])).

fof(f47,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f28,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f29,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f247,plain,
    ( ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f38,f226])).

fof(f226,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f101,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f101,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f99,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f99,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_relat_1(sK2)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f88,f92,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f92,plain,
    ( ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f71,f88,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f88,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_2
  <=> r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f165,plain,
    ( ~ spl5_2
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f71,f88,f151,f33])).

fof(f151,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f147,f90])).

fof(f90,plain,
    ( sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2))))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f88,f25])).

fof(f25,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f147,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2)))),k2_relat_1(sK2))
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f91,f130])).

fof(f130,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_7
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f91,plain,
    ( r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f88,f24])).

fof(f24,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f146,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f27,f127])).

fof(f127,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f27,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f142,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f48,f123,f36])).

fof(f123,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f48,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f135,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f26,f115])).

fof(f115,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f131,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f72,f129,f125,f121,f117,f113])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f30,f47])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f89,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f80,f86,f82])).

fof(f80,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(factoring,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1)
      | r2_hidden(sK4(X0,k2_relat_1(sK2)),X0)
      | k2_relat_1(sK2) = X0 ) ),
    inference(resolution,[],[f69,f32])).

% (26170)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f59,f35])).

fof(f59,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f36])).

fof(f57,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f44,f46,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f46,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (26151)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (26166)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.51  % (26147)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (26150)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (26148)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (26152)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (26158)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (26162)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (26158)Refutation not found, incomplete strategy% (26158)------------------------------
% 0.22/0.52  % (26158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26158)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (26158)Memory used [KB]: 10746
% 0.22/0.52  % (26158)Time elapsed: 0.109 s
% 0.22/0.52  % (26158)------------------------------
% 0.22/0.52  % (26158)------------------------------
% 0.22/0.53  % (26161)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (26153)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (26149)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (26167)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (26159)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (26151)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f319,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f89,f131,f135,f142,f146,f165,f247,f318])).
% 0.22/0.53  fof(f318,plain,(
% 0.22/0.53    ~spl5_1),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f314])).
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    $false | ~spl5_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f71,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    sK1 = k2_relat_1(sK2) | ~spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl5_1 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    sK1 != k2_relat_1(sK2)),
% 0.22/0.53    inference(superposition,[],[f29,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f28,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    ~spl5_2 | ~spl5_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f243])).
% 0.22/0.53  fof(f243,plain,(
% 0.22/0.53    $false | (~spl5_2 | ~spl5_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f38,f226])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | (~spl5_2 | ~spl5_4)),
% 0.22/0.53    inference(backward_demodulation,[],[f101,f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl5_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    spl5_4 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~r1_tarski(sK1,k2_relat_1(sK2)) | ~spl5_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f99,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_relat_1(sK2))) | ~spl5_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f88,f92,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~spl5_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f71,f88,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | ~spl5_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl5_2 <=> r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ~spl5_2 | ~spl5_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    $false | (~spl5_2 | ~spl5_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f71,f88,f151,f33])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | (~spl5_2 | ~spl5_7)),
% 0.22/0.53    inference(forward_demodulation,[],[f147,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2)))) | ~spl5_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f88,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    r2_hidden(k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2)))),k2_relat_1(sK2)) | (~spl5_2 | ~spl5_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f91,f130])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,sK0)) ) | ~spl5_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f129])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl5_7 <=> ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) | ~spl5_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f88,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    spl5_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f143])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    $false | spl5_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f27,f127])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ~v1_funct_2(sK2,sK0,sK1) | spl5_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f125])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    spl5_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    $false | spl5_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f48,f123,f36])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f121])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    spl5_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f28,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl5_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f132])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    $false | spl5_3),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f26,f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | spl5_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f113])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl5_3 <=> v1_funct_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    v1_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f72,f129,f125,f121,f117,f113])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | ~v1_funct_1(sK2)) )),
% 0.22/0.53    inference(superposition,[],[f30,f47])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl5_1 | spl5_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f80,f86,f82])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | sK1 = k2_relat_1(sK2)),
% 0.22/0.53    inference(factoring,[],[f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK4(X0,k2_relat_1(sK2)),sK1) | r2_hidden(sK4(X0,k2_relat_1(sK2)),X0) | k2_relat_1(sK2) = X0) )),
% 0.22/0.53    inference(resolution,[],[f69,f32])).
% 0.22/0.54  % (26170)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f59,f35])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f57,f36])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f44,f46,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    v5_relat_1(sK2,sK1)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f28,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f28,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (26151)------------------------------
% 0.22/0.54  % (26151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26151)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (26151)Memory used [KB]: 6268
% 0.22/0.54  % (26151)Time elapsed: 0.111 s
% 0.22/0.54  % (26151)------------------------------
% 0.22/0.54  % (26151)------------------------------
% 0.22/0.54  % (26156)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (26146)Success in time 0.173 s
%------------------------------------------------------------------------------
