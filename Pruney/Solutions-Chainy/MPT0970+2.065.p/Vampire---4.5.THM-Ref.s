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
% DateTime   : Thu Dec  3 13:00:58 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 182 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  227 ( 766 expanded)
%              Number of equality atoms :   57 ( 205 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f135,f183,f219,f223,f244,f314])).

fof(f314,plain,(
    ~ spl13_2 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f65,f279])).

fof(f279,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl13_2 ),
    inference(backward_demodulation,[],[f157,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK1
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl13_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f157,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f98,f142,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f142,plain,(
    ~ r2_hidden(sK4(sK1,sK2),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f65,f115,f45])).

fof(f115,plain,(
    ~ r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK11(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f99,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f32,f33,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f33,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,(
    r2_hidden(sK4(sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f32,f33,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X1,X2),X1)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f244,plain,(
    ~ spl13_9 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl13_9 ),
    inference(unit_resulting_resolution,[],[f98,f115,f105,f218])).

fof(f218,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(X2),sK0)
        | ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,k2_relat_1(sK2)) )
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl13_9
  <=> ! [X2] :
        ( ~ r2_hidden(sK3(X2),sK0)
        | ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f105,plain,(
    r2_hidden(sK3(sK4(sK1,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f98,f28])).

fof(f28,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f223,plain,(
    spl13_8 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl13_8 ),
    inference(unit_resulting_resolution,[],[f30,f215])).

fof(f215,plain,
    ( ~ v1_funct_1(sK2)
    | spl13_8 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl13_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f219,plain,
    ( ~ spl13_7
    | ~ spl13_8
    | spl13_9
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f136,f128,f217,f213,f170])).

fof(f170,plain,
    ( spl13_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f128,plain,
    ( spl13_3
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f136,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(X2),sK0)
        | r2_hidden(X2,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl13_3 ),
    inference(backward_demodulation,[],[f109,f130])).

fof(f130,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f109,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK3(X2),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f67,f29])).

fof(f29,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f183,plain,(
    spl13_7 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl13_7 ),
    inference(unit_resulting_resolution,[],[f50,f32,f172,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f172,plain,
    ( ~ v1_relat_1(sK2)
    | spl13_7 ),
    inference(avatar_component_clause,[],[f170])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f135,plain,(
    spl13_1 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f31,f122])).

fof(f122,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl13_1
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,
    ( ~ spl13_1
    | spl13_2
    | spl13_3 ),
    inference(avatar_split_clause,[],[f89,f128,f124,f120])).

fof(f89,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f85,f80])).

fof(f80,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f32,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f32,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:25:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (10293)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.18/0.52  % (10276)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.18/0.52  % (10268)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.18/0.52  % (10264)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.18/0.52  % (10268)Refutation found. Thanks to Tanya!
% 1.18/0.52  % SZS status Theorem for theBenchmark
% 1.18/0.52  % SZS output start Proof for theBenchmark
% 1.18/0.53  fof(f315,plain,(
% 1.18/0.53    $false),
% 1.18/0.53    inference(avatar_sat_refutation,[],[f131,f135,f183,f219,f223,f244,f314])).
% 1.18/0.53  fof(f314,plain,(
% 1.18/0.53    ~spl13_2),
% 1.18/0.53    inference(avatar_contradiction_clause,[],[f308])).
% 1.18/0.53  fof(f308,plain,(
% 1.18/0.53    $false | ~spl13_2),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f65,f279])).
% 1.18/0.53  fof(f279,plain,(
% 1.18/0.53    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl13_2),
% 1.18/0.53    inference(backward_demodulation,[],[f157,f126])).
% 1.18/0.53  fof(f126,plain,(
% 1.18/0.53    k1_xboole_0 = sK1 | ~spl13_2),
% 1.18/0.53    inference(avatar_component_clause,[],[f124])).
% 1.18/0.53  fof(f124,plain,(
% 1.18/0.53    spl13_2 <=> k1_xboole_0 = sK1),
% 1.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.18/0.53  fof(f157,plain,(
% 1.18/0.53    ~r1_tarski(sK1,k1_xboole_0)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f98,f142,f45])).
% 1.18/0.53  fof(f45,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f23])).
% 1.18/0.53  fof(f23,plain,(
% 1.18/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.18/0.53    inference(ennf_transformation,[],[f1])).
% 1.18/0.53  fof(f1,axiom,(
% 1.18/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.18/0.53  fof(f142,plain,(
% 1.18/0.53    ~r2_hidden(sK4(sK1,sK2),k1_xboole_0)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f65,f115,f45])).
% 1.18/0.53  fof(f115,plain,(
% 1.18/0.53    ~r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f99,f75])).
% 1.18/0.53  fof(f75,plain,(
% 1.18/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK11(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.18/0.53    inference(equality_resolution,[],[f58])).
% 1.18/0.53  fof(f58,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK11(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.18/0.53    inference(cnf_transformation,[],[f5])).
% 1.18/0.53  fof(f5,axiom,(
% 1.18/0.53    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.18/0.53  fof(f99,plain,(
% 1.18/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK1,sK2)),sK2)) )),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f32,f33,f35])).
% 1.18/0.53  fof(f35,plain,(
% 1.18/0.53    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X4,sK4(X1,X2)),X2)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f18])).
% 1.18/0.53  fof(f18,plain,(
% 1.18/0.53    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/0.53    inference(ennf_transformation,[],[f12])).
% 1.18/0.53  fof(f12,axiom,(
% 1.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 1.18/0.53  fof(f33,plain,(
% 1.18/0.53    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.18/0.53    inference(cnf_transformation,[],[f17])).
% 1.18/0.53  fof(f17,plain,(
% 1.18/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.18/0.53    inference(flattening,[],[f16])).
% 1.18/0.53  fof(f16,plain,(
% 1.18/0.53    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.18/0.53    inference(ennf_transformation,[],[f15])).
% 1.18/0.53  fof(f15,negated_conjecture,(
% 1.18/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.18/0.53    inference(negated_conjecture,[],[f14])).
% 1.18/0.53  fof(f14,conjecture,(
% 1.18/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 1.18/0.53  fof(f32,plain,(
% 1.18/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.18/0.53    inference(cnf_transformation,[],[f17])).
% 1.18/0.53  fof(f98,plain,(
% 1.18/0.53    r2_hidden(sK4(sK1,sK2),sK1)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f32,f33,f34])).
% 1.18/0.53  fof(f34,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK4(X1,X2),X1) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.18/0.53    inference(cnf_transformation,[],[f18])).
% 1.18/0.53  fof(f65,plain,(
% 1.18/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f2])).
% 1.18/0.53  fof(f2,axiom,(
% 1.18/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.18/0.53  fof(f244,plain,(
% 1.18/0.53    ~spl13_9),
% 1.18/0.53    inference(avatar_contradiction_clause,[],[f238])).
% 1.18/0.53  fof(f238,plain,(
% 1.18/0.53    $false | ~spl13_9),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f98,f115,f105,f218])).
% 1.18/0.53  fof(f218,plain,(
% 1.18/0.53    ( ! [X2] : (~r2_hidden(sK3(X2),sK0) | ~r2_hidden(X2,sK1) | r2_hidden(X2,k2_relat_1(sK2))) ) | ~spl13_9),
% 1.18/0.53    inference(avatar_component_clause,[],[f217])).
% 1.18/0.53  fof(f217,plain,(
% 1.18/0.53    spl13_9 <=> ! [X2] : (~r2_hidden(sK3(X2),sK0) | ~r2_hidden(X2,sK1) | r2_hidden(X2,k2_relat_1(sK2)))),
% 1.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 1.18/0.53  fof(f105,plain,(
% 1.18/0.53    r2_hidden(sK3(sK4(sK1,sK2)),sK0)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f98,f28])).
% 1.18/0.53  fof(f28,plain,(
% 1.18/0.53    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f17])).
% 1.18/0.53  fof(f223,plain,(
% 1.18/0.53    spl13_8),
% 1.18/0.53    inference(avatar_contradiction_clause,[],[f220])).
% 1.18/0.53  fof(f220,plain,(
% 1.18/0.53    $false | spl13_8),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f30,f215])).
% 1.18/0.53  fof(f215,plain,(
% 1.18/0.53    ~v1_funct_1(sK2) | spl13_8),
% 1.18/0.53    inference(avatar_component_clause,[],[f213])).
% 1.18/0.53  fof(f213,plain,(
% 1.18/0.53    spl13_8 <=> v1_funct_1(sK2)),
% 1.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).
% 1.18/0.53  fof(f30,plain,(
% 1.18/0.53    v1_funct_1(sK2)),
% 1.18/0.53    inference(cnf_transformation,[],[f17])).
% 1.18/0.53  fof(f219,plain,(
% 1.18/0.53    ~spl13_7 | ~spl13_8 | spl13_9 | ~spl13_3),
% 1.18/0.53    inference(avatar_split_clause,[],[f136,f128,f217,f213,f170])).
% 1.18/0.53  fof(f170,plain,(
% 1.18/0.53    spl13_7 <=> v1_relat_1(sK2)),
% 1.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 1.18/0.53  fof(f128,plain,(
% 1.18/0.53    spl13_3 <=> sK0 = k1_relat_1(sK2)),
% 1.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.18/0.53  fof(f136,plain,(
% 1.18/0.53    ( ! [X2] : (~r2_hidden(sK3(X2),sK0) | r2_hidden(X2,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X2,sK1)) ) | ~spl13_3),
% 1.18/0.53    inference(backward_demodulation,[],[f109,f130])).
% 1.18/0.53  fof(f130,plain,(
% 1.18/0.53    sK0 = k1_relat_1(sK2) | ~spl13_3),
% 1.18/0.53    inference(avatar_component_clause,[],[f128])).
% 1.18/0.53  fof(f109,plain,(
% 1.18/0.53    ( ! [X2] : (r2_hidden(X2,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(sK3(X2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X2,sK1)) )),
% 1.18/0.53    inference(superposition,[],[f67,f29])).
% 1.18/0.53  fof(f29,plain,(
% 1.18/0.53    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f17])).
% 1.18/0.53  fof(f67,plain,(
% 1.18/0.53    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.18/0.53    inference(equality_resolution,[],[f66])).
% 1.18/0.53  fof(f66,plain,(
% 1.18/0.53    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.18/0.53    inference(equality_resolution,[],[f43])).
% 1.18/0.53  fof(f43,plain,(
% 1.18/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.18/0.53    inference(cnf_transformation,[],[f21])).
% 1.18/0.53  fof(f21,plain,(
% 1.18/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.18/0.53    inference(flattening,[],[f20])).
% 1.18/0.53  fof(f20,plain,(
% 1.18/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.18/0.53    inference(ennf_transformation,[],[f8])).
% 1.18/0.53  fof(f8,axiom,(
% 1.18/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.18/0.53  fof(f183,plain,(
% 1.18/0.53    spl13_7),
% 1.18/0.53    inference(avatar_contradiction_clause,[],[f178])).
% 1.18/0.53  fof(f178,plain,(
% 1.18/0.53    $false | spl13_7),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f50,f32,f172,f64])).
% 1.18/0.53  fof(f64,plain,(
% 1.18/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f27])).
% 1.18/0.53  fof(f27,plain,(
% 1.18/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.18/0.53    inference(ennf_transformation,[],[f4])).
% 1.18/0.53  fof(f4,axiom,(
% 1.18/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.18/0.53  fof(f172,plain,(
% 1.18/0.53    ~v1_relat_1(sK2) | spl13_7),
% 1.18/0.53    inference(avatar_component_clause,[],[f170])).
% 1.18/0.53  fof(f50,plain,(
% 1.18/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.18/0.53    inference(cnf_transformation,[],[f6])).
% 1.18/0.53  fof(f6,axiom,(
% 1.18/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.18/0.53  fof(f135,plain,(
% 1.18/0.53    spl13_1),
% 1.18/0.53    inference(avatar_contradiction_clause,[],[f132])).
% 1.18/0.53  fof(f132,plain,(
% 1.18/0.53    $false | spl13_1),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f31,f122])).
% 1.18/0.53  fof(f122,plain,(
% 1.18/0.53    ~v1_funct_2(sK2,sK0,sK1) | spl13_1),
% 1.18/0.53    inference(avatar_component_clause,[],[f120])).
% 1.18/0.53  fof(f120,plain,(
% 1.18/0.53    spl13_1 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.18/0.53  fof(f31,plain,(
% 1.18/0.53    v1_funct_2(sK2,sK0,sK1)),
% 1.18/0.53    inference(cnf_transformation,[],[f17])).
% 1.18/0.53  fof(f131,plain,(
% 1.18/0.53    ~spl13_1 | spl13_2 | spl13_3),
% 1.18/0.53    inference(avatar_split_clause,[],[f89,f128,f124,f120])).
% 1.18/0.53  fof(f89,plain,(
% 1.18/0.53    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 1.18/0.53    inference(forward_demodulation,[],[f85,f80])).
% 1.18/0.53  fof(f80,plain,(
% 1.18/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.18/0.53    inference(unit_resulting_resolution,[],[f32,f63])).
% 1.18/0.53  fof(f63,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f26])).
% 1.18/0.53  fof(f26,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/0.53    inference(ennf_transformation,[],[f10])).
% 1.18/0.53  fof(f10,axiom,(
% 1.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.18/0.53  fof(f85,plain,(
% 1.18/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.18/0.53    inference(resolution,[],[f32,f56])).
% 1.18/0.53  fof(f56,plain,(
% 1.18/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.18/0.53    inference(cnf_transformation,[],[f25])).
% 1.18/0.53  fof(f25,plain,(
% 1.18/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/0.53    inference(flattening,[],[f24])).
% 1.18/0.53  fof(f24,plain,(
% 1.18/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/0.53    inference(ennf_transformation,[],[f13])).
% 1.18/0.53  fof(f13,axiom,(
% 1.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.18/0.53  % SZS output end Proof for theBenchmark
% 1.18/0.53  % (10268)------------------------------
% 1.18/0.53  % (10268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (10268)Termination reason: Refutation
% 1.18/0.53  
% 1.18/0.53  % (10268)Memory used [KB]: 6396
% 1.18/0.53  % (10268)Time elapsed: 0.103 s
% 1.18/0.53  % (10268)------------------------------
% 1.18/0.53  % (10268)------------------------------
% 1.18/0.53  % (10263)Success in time 0.165 s
%------------------------------------------------------------------------------
