%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 360 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  330 (1345 expanded)
%              Number of equality atoms :   83 ( 390 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12438)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (12454)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f1104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f162,f189,f196,f308,f315,f418,f588,f960,f1001,f1103])).

fof(f1103,plain,
    ( ~ spl8_7
    | spl8_9
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f1099])).

fof(f1099,plain,
    ( $false
    | ~ spl8_7
    | spl8_9
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f307,f1051])).

fof(f1051,plain,
    ( k1_xboole_0 != sK0
    | ~ spl8_7
    | spl8_9
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f187,f1040])).

fof(f1040,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl8_7
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f1017,f644])).

fof(f644,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ spl8_7
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f603,f590,f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
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

fof(f590,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl8_7
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f179,f307])).

fof(f179,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl8_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f603,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f28,f307])).

fof(f28,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
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

fof(f1017,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f781,f307])).

fof(f781,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f29,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f187,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl8_9
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f307,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl8_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1001,plain,(
    ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f997])).

fof(f997,plain,
    ( $false
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f68,f94,f95,f101,f959])).

fof(f959,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(sK3(X3),sK0)
        | ~ r1_tarski(X4,sK1)
        | ~ r2_hidden(X3,X4)
        | r2_hidden(X3,k2_relat_1(sK2)) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f958])).

fof(f958,plain,
    ( spl8_24
  <=> ! [X3,X4] :
        ( ~ r2_hidden(sK3(X3),sK0)
        | ~ r1_tarski(X4,sK1)
        | ~ r2_hidden(X3,X4)
        | r2_hidden(X3,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f101,plain,(
    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f94,f25])).

fof(f25,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    ~ r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f92,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f92,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f84,f89,f57])).

fof(f57,plain,(
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

fof(f89,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f30,f73])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f79,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f74,f73])).

fof(f74,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f94,plain,(
    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f92,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f960,plain,
    ( ~ spl8_6
    | ~ spl8_13
    | spl8_24
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f762,f186,f958,f578,f149])).

fof(f149,plain,
    ( spl8_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f578,plain,
    ( spl8_13
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f762,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(sK3(X3),sK0)
        | r2_hidden(X3,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X3,X4)
        | ~ r1_tarski(X4,sK1) )
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f687,f188])).

fof(f188,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f687,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK3(X3),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,sK1) ) ),
    inference(superposition,[],[f59,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK2,sK3(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f588,plain,(
    spl8_13 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f27,f580])).

fof(f580,plain,
    ( ~ v1_funct_1(sK2)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f578])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f418,plain,
    ( ~ spl8_8
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f68,f367])).

fof(f367,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f332,f50])).

fof(f50,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f332,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f208,f303])).

fof(f303,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f208,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f92,f184])).

fof(f184,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl8_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f315,plain,
    ( ~ spl8_8
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl8_8
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f204,f299,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f299,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl8_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f204,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f75,f184])).

fof(f75,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f54])).

fof(f308,plain,
    ( ~ spl8_10
    | spl8_11
    | spl8_12
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f230,f182,f305,f301,f297])).

fof(f230,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_8 ),
    inference(resolution,[],[f199,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f199,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f28,f184])).

fof(f196,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f75,f180,f53])).

fof(f180,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f178])).

fof(f189,plain,
    ( ~ spl8_7
    | spl8_8
    | spl8_9 ),
    inference(avatar_split_clause,[],[f80,f186,f182,f178])).

fof(f80,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f71,f72])).

fof(f72,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f29,f51])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f28,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f162,plain,(
    spl8_6 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f42,f29,f151,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f151,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f149])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:00:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (12453)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (12445)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (12437)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (12434)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12435)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (12440)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (12433)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (12439)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (12436)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (12442)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (12443)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (12432)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (12457)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (12431)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (12452)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (12440)Refutation not found, incomplete strategy% (12440)------------------------------
% 0.21/0.54  % (12440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12440)Memory used [KB]: 10746
% 0.21/0.54  % (12440)Time elapsed: 0.136 s
% 0.21/0.54  % (12440)------------------------------
% 0.21/0.54  % (12440)------------------------------
% 0.21/0.54  % (12458)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (12459)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (12446)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (12456)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (12450)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (12451)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (12455)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (12449)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (12448)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (12444)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (12441)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (12447)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (12430)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (12434)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.58  % (12438)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.60/0.59  % (12454)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.60/0.59  fof(f1104,plain,(
% 1.60/0.59    $false),
% 1.60/0.59    inference(avatar_sat_refutation,[],[f162,f189,f196,f308,f315,f418,f588,f960,f1001,f1103])).
% 1.60/0.59  fof(f1103,plain,(
% 1.60/0.59    ~spl8_7 | spl8_9 | ~spl8_12),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f1099])).
% 1.60/0.59  fof(f1099,plain,(
% 1.60/0.59    $false | (~spl8_7 | spl8_9 | ~spl8_12)),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f307,f1051])).
% 1.60/0.59  fof(f1051,plain,(
% 1.60/0.59    k1_xboole_0 != sK0 | (~spl8_7 | spl8_9 | ~spl8_12)),
% 1.60/0.59    inference(forward_demodulation,[],[f187,f1040])).
% 1.60/0.59  fof(f1040,plain,(
% 1.60/0.59    k1_xboole_0 = k1_relat_1(sK2) | (~spl8_7 | ~spl8_12)),
% 1.60/0.59    inference(forward_demodulation,[],[f1017,f644])).
% 1.60/0.59  fof(f644,plain,(
% 1.60/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) | (~spl8_7 | ~spl8_12)),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f603,f590,f62])).
% 1.60/0.59  fof(f62,plain,(
% 1.60/0.59    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.60/0.59    inference(equality_resolution,[],[f46])).
% 1.60/0.59  fof(f46,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  fof(f22,plain,(
% 1.60/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.59    inference(flattening,[],[f21])).
% 1.60/0.59  fof(f21,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.59    inference(ennf_transformation,[],[f11])).
% 1.60/0.59  fof(f11,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.60/0.59  fof(f590,plain,(
% 1.60/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl8_7 | ~spl8_12)),
% 1.60/0.59    inference(forward_demodulation,[],[f179,f307])).
% 1.60/0.59  fof(f179,plain,(
% 1.60/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_7),
% 1.60/0.59    inference(avatar_component_clause,[],[f178])).
% 1.60/0.59  fof(f178,plain,(
% 1.60/0.59    spl8_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.60/0.59  fof(f603,plain,(
% 1.60/0.59    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl8_12),
% 1.60/0.59    inference(forward_demodulation,[],[f28,f307])).
% 1.60/0.59  fof(f28,plain,(
% 1.60/0.59    v1_funct_2(sK2,sK0,sK1)),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f15,plain,(
% 1.60/0.59    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.60/0.59    inference(flattening,[],[f14])).
% 1.60/0.59  fof(f14,plain,(
% 1.60/0.59    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.60/0.59    inference(ennf_transformation,[],[f13])).
% 1.60/0.59  fof(f13,negated_conjecture,(
% 1.60/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.60/0.59    inference(negated_conjecture,[],[f12])).
% 1.60/0.59  fof(f12,conjecture,(
% 1.60/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 1.60/0.59  fof(f1017,plain,(
% 1.60/0.59    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2) | ~spl8_12),
% 1.60/0.59    inference(backward_demodulation,[],[f781,f307])).
% 1.60/0.59  fof(f781,plain,(
% 1.60/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.60/0.59    inference(resolution,[],[f29,f51])).
% 1.60/0.59  fof(f51,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f23])).
% 1.60/0.59  fof(f23,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.59    inference(ennf_transformation,[],[f9])).
% 1.60/0.59  fof(f9,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.60/0.59  fof(f29,plain,(
% 1.60/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f187,plain,(
% 1.60/0.59    sK0 != k1_relat_1(sK2) | spl8_9),
% 1.60/0.59    inference(avatar_component_clause,[],[f186])).
% 1.60/0.59  fof(f186,plain,(
% 1.60/0.59    spl8_9 <=> sK0 = k1_relat_1(sK2)),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.60/0.59  fof(f307,plain,(
% 1.60/0.59    k1_xboole_0 = sK0 | ~spl8_12),
% 1.60/0.59    inference(avatar_component_clause,[],[f305])).
% 1.60/0.59  fof(f305,plain,(
% 1.60/0.59    spl8_12 <=> k1_xboole_0 = sK0),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.60/0.59  fof(f1001,plain,(
% 1.60/0.59    ~spl8_24),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f997])).
% 1.60/0.59  fof(f997,plain,(
% 1.60/0.59    $false | ~spl8_24),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f68,f94,f95,f101,f959])).
% 1.60/0.59  fof(f959,plain,(
% 1.60/0.59    ( ! [X4,X3] : (~r2_hidden(sK3(X3),sK0) | ~r1_tarski(X4,sK1) | ~r2_hidden(X3,X4) | r2_hidden(X3,k2_relat_1(sK2))) ) | ~spl8_24),
% 1.60/0.59    inference(avatar_component_clause,[],[f958])).
% 1.60/0.59  fof(f958,plain,(
% 1.60/0.59    spl8_24 <=> ! [X3,X4] : (~r2_hidden(sK3(X3),sK0) | ~r1_tarski(X4,sK1) | ~r2_hidden(X3,X4) | r2_hidden(X3,k2_relat_1(sK2)))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.60/0.59  fof(f101,plain,(
% 1.60/0.59    r2_hidden(sK3(sK7(sK1,k2_relat_1(sK2))),sK0)),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f94,f25])).
% 1.60/0.59  fof(f25,plain,(
% 1.60/0.59    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f95,plain,(
% 1.60/0.59    ~r2_hidden(sK7(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f92,f41])).
% 1.60/0.59  fof(f41,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f20])).
% 1.60/0.59  fof(f20,plain,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f1])).
% 1.60/0.59  fof(f1,axiom,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.60/0.59  fof(f92,plain,(
% 1.60/0.59    ~r1_tarski(sK1,k2_relat_1(sK2))),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f84,f89,f57])).
% 1.60/0.59  fof(f57,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f2])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.59  fof(f89,plain,(
% 1.60/0.59    sK1 != k2_relat_1(sK2)),
% 1.60/0.59    inference(superposition,[],[f30,f73])).
% 1.60/0.59  fof(f73,plain,(
% 1.60/0.59    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f29,f32])).
% 1.60/0.59  fof(f32,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f17])).
% 1.60/0.59  fof(f17,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.59    inference(ennf_transformation,[],[f10])).
% 1.60/0.59  fof(f10,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.60/0.59  fof(f30,plain,(
% 1.60/0.59    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f84,plain,(
% 1.60/0.59    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f79,f54])).
% 1.60/0.59  fof(f54,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f3])).
% 1.60/0.59  fof(f3,axiom,(
% 1.60/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.60/0.59  fof(f79,plain,(
% 1.60/0.59    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.60/0.59    inference(backward_demodulation,[],[f74,f73])).
% 1.60/0.59  fof(f74,plain,(
% 1.60/0.59    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f29,f31])).
% 1.60/0.59  fof(f31,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f16])).
% 1.60/0.59  fof(f16,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.59    inference(ennf_transformation,[],[f8])).
% 1.60/0.59  fof(f8,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.60/0.59  fof(f94,plain,(
% 1.60/0.59    r2_hidden(sK7(sK1,k2_relat_1(sK2)),sK1)),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f92,f40])).
% 1.60/0.59  fof(f40,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f20])).
% 1.60/0.59  fof(f68,plain,(
% 1.60/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.59    inference(equality_resolution,[],[f55])).
% 1.60/0.59  fof(f55,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f2])).
% 1.60/0.59  fof(f960,plain,(
% 1.60/0.59    ~spl8_6 | ~spl8_13 | spl8_24 | ~spl8_9),
% 1.60/0.59    inference(avatar_split_clause,[],[f762,f186,f958,f578,f149])).
% 1.60/0.59  fof(f149,plain,(
% 1.60/0.59    spl8_6 <=> v1_relat_1(sK2)),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.60/0.59  fof(f578,plain,(
% 1.60/0.59    spl8_13 <=> v1_funct_1(sK2)),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.60/0.59  fof(f762,plain,(
% 1.60/0.59    ( ! [X4,X3] : (~r2_hidden(sK3(X3),sK0) | r2_hidden(X3,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X3,X4) | ~r1_tarski(X4,sK1)) ) | ~spl8_9),
% 1.60/0.59    inference(backward_demodulation,[],[f687,f188])).
% 1.60/0.59  fof(f188,plain,(
% 1.60/0.59    sK0 = k1_relat_1(sK2) | ~spl8_9),
% 1.60/0.59    inference(avatar_component_clause,[],[f186])).
% 1.60/0.59  fof(f687,plain,(
% 1.60/0.59    ( ! [X4,X3] : (r2_hidden(X3,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(X3),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X3,X4) | ~r1_tarski(X4,sK1)) )),
% 1.60/0.59    inference(superposition,[],[f59,f98])).
% 1.60/0.59  fof(f98,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k1_funct_1(sK2,sK3(X0)) = X0 | ~r2_hidden(X0,X1) | ~r1_tarski(X1,sK1)) )),
% 1.60/0.59    inference(resolution,[],[f26,f39])).
% 1.60/0.59  fof(f39,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f20])).
% 1.60/0.59  fof(f26,plain,(
% 1.60/0.59    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f59,plain,(
% 1.60/0.59    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.59    inference(equality_resolution,[],[f58])).
% 1.60/0.59  fof(f58,plain,(
% 1.60/0.59    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.60/0.59    inference(equality_resolution,[],[f38])).
% 1.60/0.59  fof(f38,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f19])).
% 1.60/0.59  fof(f19,plain,(
% 1.60/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.59    inference(flattening,[],[f18])).
% 1.60/0.59  fof(f18,plain,(
% 1.60/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f7])).
% 1.60/0.59  fof(f7,axiom,(
% 1.60/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.60/0.59  fof(f588,plain,(
% 1.60/0.59    spl8_13),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f585])).
% 1.60/0.59  fof(f585,plain,(
% 1.60/0.59    $false | spl8_13),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f27,f580])).
% 1.60/0.59  fof(f580,plain,(
% 1.60/0.59    ~v1_funct_1(sK2) | spl8_13),
% 1.60/0.59    inference(avatar_component_clause,[],[f578])).
% 1.60/0.59  fof(f27,plain,(
% 1.60/0.59    v1_funct_1(sK2)),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f418,plain,(
% 1.60/0.59    ~spl8_8 | ~spl8_11),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f408])).
% 1.60/0.59  fof(f408,plain,(
% 1.60/0.59    $false | (~spl8_8 | ~spl8_11)),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f68,f367])).
% 1.60/0.59  fof(f367,plain,(
% 1.60/0.59    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl8_8 | ~spl8_11)),
% 1.60/0.59    inference(forward_demodulation,[],[f332,f50])).
% 1.60/0.59  fof(f50,plain,(
% 1.60/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.60/0.59    inference(cnf_transformation,[],[f6])).
% 1.60/0.59  fof(f6,axiom,(
% 1.60/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.60/0.59  fof(f332,plain,(
% 1.60/0.59    ~r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl8_8 | ~spl8_11)),
% 1.60/0.59    inference(backward_demodulation,[],[f208,f303])).
% 1.60/0.59  fof(f303,plain,(
% 1.60/0.59    k1_xboole_0 = sK2 | ~spl8_11),
% 1.60/0.59    inference(avatar_component_clause,[],[f301])).
% 1.60/0.59  fof(f301,plain,(
% 1.60/0.59    spl8_11 <=> k1_xboole_0 = sK2),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.60/0.59  fof(f208,plain,(
% 1.60/0.59    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | ~spl8_8),
% 1.60/0.59    inference(backward_demodulation,[],[f92,f184])).
% 1.60/0.59  fof(f184,plain,(
% 1.60/0.59    k1_xboole_0 = sK1 | ~spl8_8),
% 1.60/0.59    inference(avatar_component_clause,[],[f182])).
% 1.60/0.59  fof(f182,plain,(
% 1.60/0.59    spl8_8 <=> k1_xboole_0 = sK1),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.60/0.59  fof(f315,plain,(
% 1.60/0.59    ~spl8_8 | spl8_10),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f311])).
% 1.60/0.59  fof(f311,plain,(
% 1.60/0.59    $false | (~spl8_8 | spl8_10)),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f204,f299,f53])).
% 1.60/0.59  fof(f53,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f3])).
% 1.60/0.59  fof(f299,plain,(
% 1.60/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | spl8_10),
% 1.60/0.59    inference(avatar_component_clause,[],[f297])).
% 1.60/0.59  fof(f297,plain,(
% 1.60/0.59    spl8_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.60/0.59  fof(f204,plain,(
% 1.60/0.59    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl8_8),
% 1.60/0.59    inference(backward_demodulation,[],[f75,f184])).
% 1.60/0.59  fof(f75,plain,(
% 1.60/0.59    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f29,f54])).
% 1.60/0.59  fof(f308,plain,(
% 1.60/0.59    ~spl8_10 | spl8_11 | spl8_12 | ~spl8_8),
% 1.60/0.59    inference(avatar_split_clause,[],[f230,f182,f305,f301,f297])).
% 1.60/0.59  fof(f230,plain,(
% 1.60/0.59    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_8),
% 1.60/0.59    inference(resolution,[],[f199,f64])).
% 1.60/0.59  fof(f64,plain,(
% 1.60/0.59    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.60/0.59    inference(equality_resolution,[],[f44])).
% 1.60/0.59  fof(f44,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  fof(f199,plain,(
% 1.60/0.59    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl8_8),
% 1.60/0.59    inference(backward_demodulation,[],[f28,f184])).
% 1.60/0.59  fof(f196,plain,(
% 1.60/0.59    spl8_7),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f192])).
% 1.60/0.59  fof(f192,plain,(
% 1.60/0.59    $false | spl8_7),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f75,f180,f53])).
% 1.60/0.59  fof(f180,plain,(
% 1.60/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl8_7),
% 1.60/0.59    inference(avatar_component_clause,[],[f178])).
% 1.60/0.59  fof(f189,plain,(
% 1.60/0.59    ~spl8_7 | spl8_8 | spl8_9),
% 1.60/0.59    inference(avatar_split_clause,[],[f80,f186,f182,f178])).
% 1.60/0.59  fof(f80,plain,(
% 1.60/0.59    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.60/0.59    inference(backward_demodulation,[],[f71,f72])).
% 1.60/0.59  fof(f72,plain,(
% 1.60/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f29,f51])).
% 1.60/0.59  fof(f71,plain,(
% 1.60/0.59    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.60/0.59    inference(resolution,[],[f28,f48])).
% 1.60/0.59  fof(f48,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  fof(f162,plain,(
% 1.60/0.59    spl8_6),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f157])).
% 1.60/0.59  fof(f157,plain,(
% 1.60/0.59    $false | spl8_6),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f42,f29,f151,f52])).
% 1.60/0.59  fof(f52,plain,(
% 1.60/0.59    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f24])).
% 1.60/0.59  fof(f24,plain,(
% 1.60/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.60/0.59    inference(ennf_transformation,[],[f4])).
% 1.60/0.59  fof(f4,axiom,(
% 1.60/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.60/0.59  fof(f151,plain,(
% 1.60/0.59    ~v1_relat_1(sK2) | spl8_6),
% 1.60/0.59    inference(avatar_component_clause,[],[f149])).
% 1.60/0.59  fof(f42,plain,(
% 1.60/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f5])).
% 1.60/0.59  fof(f5,axiom,(
% 1.60/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.60/0.59  % SZS output end Proof for theBenchmark
% 1.60/0.59  % (12434)------------------------------
% 1.60/0.59  % (12434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (12434)Termination reason: Refutation
% 1.60/0.59  
% 1.60/0.59  % (12434)Memory used [KB]: 6524
% 1.60/0.59  % (12434)Time elapsed: 0.149 s
% 1.60/0.59  % (12434)------------------------------
% 1.60/0.59  % (12434)------------------------------
% 1.60/0.59  % (12429)Success in time 0.229 s
%------------------------------------------------------------------------------
