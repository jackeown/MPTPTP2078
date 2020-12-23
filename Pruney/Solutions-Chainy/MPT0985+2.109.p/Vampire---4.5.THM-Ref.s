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
% DateTime   : Thu Dec  3 13:02:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 722 expanded)
%              Number of leaves         :   18 ( 166 expanded)
%              Depth                    :   18
%              Number of atoms          :  379 (3196 expanded)
%              Number of equality atoms :   95 ( 602 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1052,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f153,f161,f252,f425,f502,f526,f530,f700,f1051])).

fof(f1051,plain,
    ( spl4_2
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f1048])).

fof(f1048,plain,
    ( $false
    | spl4_2
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f114,f927])).

fof(f927,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_6 ),
    inference(backward_demodulation,[],[f92,f922])).

fof(f922,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl4_6 ),
    inference(backward_demodulation,[],[f71,f918])).

fof(f918,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f152,f35,f36,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

% (18415)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

% (18413)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f152,plain,
    ( k1_xboole_0 != sK1
    | spl4_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f71,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f36,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f92,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f91,f84])).

fof(f84,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f76,f74])).

fof(f74,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f73,f38])).

fof(f38,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f76,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f37,f72,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f72,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f37,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f85,f77])).

fof(f77,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f37,f72,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f78,f79,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

% (18406)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f79,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f72,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f78,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f72,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f114,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f700,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f72,f34,f118,f42])).

fof(f118,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_3
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f530,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f305,f501])).

fof(f501,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl4_9
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f305,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f270,f144])).

fof(f144,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f270,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f256,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

% (18403)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f256,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f36,f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f526,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f523])).

% (18422)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f523,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f305,f522])).

fof(f522,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_6
    | spl4_8 ),
    inference(forward_demodulation,[],[f521,f63])).

fof(f63,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f521,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_4
    | ~ spl4_6
    | spl4_8 ),
    inference(trivial_inequality_removal,[],[f520])).

fof(f520,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_4
    | ~ spl4_6
    | spl4_8 ),
    inference(forward_demodulation,[],[f517,f368])).

fof(f368,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f347,f298])).

fof(f298,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f259,f144])).

% (18415)Refutation not found, incomplete strategy% (18415)------------------------------
% (18415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18415)Termination reason: Refutation not found, incomplete strategy

% (18415)Memory used [KB]: 10874
% (18415)Time elapsed: 0.134 s
% (18415)------------------------------
% (18415)------------------------------
fof(f259,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f74,f151])).

fof(f347,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f277,f342])).

fof(f342,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f278,f300,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f300,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f262,f144])).

fof(f262,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f84,f151])).

fof(f278,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f78,f144])).

fof(f277,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f77,f144])).

fof(f517,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_8 ),
    inference(superposition,[],[f497,f58])).

fof(f497,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f495])).

fof(f495,plain,
    ( spl4_8
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f502,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f443,f150,f142,f112,f499,f495])).

fof(f443,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f441,f63])).

fof(f441,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f440,f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f440,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f439,f342])).

fof(f439,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f438,f144])).

fof(f438,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f114,f151])).

fof(f425,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f305,f367])).

fof(f367,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f307,f342])).

fof(f307,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f273,f144])).

fof(f273,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_1
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f266,f63])).

fof(f266,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f110,f151])).

fof(f110,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_1
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f252,plain,
    ( spl4_1
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl4_1
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f110,f172])).

fof(f172,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_6 ),
    inference(backward_demodulation,[],[f90,f168])).

fof(f168,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl4_6 ),
    inference(backward_demodulation,[],[f71,f166])).

fof(f166,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f35,f36,f152,f57])).

fof(f90,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f89,f84])).

fof(f89,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f86,f77])).

fof(f86,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(unit_resulting_resolution,[],[f78,f79,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f161,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f36,f148,f49])).

fof(f148,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f153,plain,
    ( spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f97,f150,f146,f142])).

fof(f97,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f47,f74])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f119,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f33,f116,f112,f108])).

fof(f33,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (18397)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (18399)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (18411)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (18393)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (18405)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (18402)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (18394)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (18420)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (18398)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (18416)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (18408)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (18396)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (18397)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (18419)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (18414)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (18400)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (18418)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (18412)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1052,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f119,f153,f161,f252,f425,f502,f526,f530,f700,f1051])).
% 0.21/0.53  fof(f1051,plain,(
% 0.21/0.53    spl4_2 | spl4_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1048])).
% 0.21/0.53  fof(f1048,plain,(
% 0.21/0.53    $false | (spl4_2 | spl4_6)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f114,f927])).
% 0.21/0.53  fof(f927,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_6),
% 0.21/0.53    inference(backward_demodulation,[],[f92,f922])).
% 0.21/0.53  fof(f922,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK2) | spl4_6),
% 0.21/0.53    inference(backward_demodulation,[],[f71,f918])).
% 0.21/0.53  fof(f918,plain,(
% 0.21/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | spl4_6),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f152,f35,f36,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  % (18415)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f16])).
% 0.21/0.53  fof(f16,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.53  % (18413)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    spl4_6 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f36,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f91,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f76,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    sK1 = k2_relat_1(sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f73,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f36,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f34,f37,f72,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f36,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v2_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f85,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f34,f37,f72,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f78,f79,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  % (18406)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f34,f72,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f34,f72,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f700,plain,(
% 0.21/0.53    spl4_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f698])).
% 0.21/0.53  fof(f698,plain,(
% 0.21/0.53    $false | spl4_3),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f72,f34,f118,f42])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ~v1_funct_1(k2_funct_1(sK2)) | spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f116])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl4_3 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f530,plain,(
% 0.21/0.53    ~spl4_4 | ~spl4_6 | spl4_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f527])).
% 0.21/0.53  fof(f527,plain,(
% 0.21/0.53    $false | (~spl4_4 | ~spl4_6 | spl4_9)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f305,f501])).
% 0.21/0.53  fof(f501,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f499])).
% 0.21/0.53  fof(f499,plain,(
% 0.21/0.53    spl4_9 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(backward_demodulation,[],[f270,f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f142])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    spl4_4 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_6),
% 0.21/0.53    inference(forward_demodulation,[],[f256,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.53  % (18403)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_6),
% 0.21/0.53    inference(backward_demodulation,[],[f36,f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f150])).
% 0.21/0.53  fof(f526,plain,(
% 0.21/0.53    ~spl4_4 | ~spl4_6 | spl4_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f523])).
% 0.21/0.53  % (18422)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  fof(f523,plain,(
% 0.21/0.53    $false | (~spl4_4 | ~spl4_6 | spl4_8)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f305,f522])).
% 0.21/0.53  fof(f522,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_4 | ~spl4_6 | spl4_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f521,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f521,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_4 | ~spl4_6 | spl4_8)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f520])).
% 0.21/0.53  fof(f520,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_4 | ~spl4_6 | spl4_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f517,f368])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f347,f298])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(backward_demodulation,[],[f259,f144])).
% 0.21/0.53  % (18415)Refutation not found, incomplete strategy% (18415)------------------------------
% 0.21/0.53  % (18415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18415)Memory used [KB]: 10874
% 0.21/0.53  % (18415)Time elapsed: 0.134 s
% 0.21/0.53  % (18415)------------------------------
% 0.21/0.53  % (18415)------------------------------
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_6),
% 0.21/0.53    inference(backward_demodulation,[],[f74,f151])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) | (~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(backward_demodulation,[],[f277,f342])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f278,f300,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(backward_demodulation,[],[f262,f144])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_6),
% 0.21/0.53    inference(backward_demodulation,[],[f84,f151])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    v1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl4_4),
% 0.21/0.53    inference(backward_demodulation,[],[f78,f144])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~spl4_4),
% 0.21/0.53    inference(backward_demodulation,[],[f77,f144])).
% 0.21/0.53  fof(f517,plain,(
% 0.21/0.53    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl4_8),
% 0.21/0.53    inference(superposition,[],[f497,f58])).
% 0.21/0.53  fof(f497,plain,(
% 0.21/0.53    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | spl4_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f495])).
% 0.21/0.53  fof(f495,plain,(
% 0.21/0.53    spl4_8 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.53  fof(f502,plain,(
% 0.21/0.53    ~spl4_8 | ~spl4_9 | spl4_2 | ~spl4_4 | ~spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f443,f150,f142,f112,f499,f495])).
% 0.21/0.53  fof(f443,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f441,f63])).
% 0.21/0.53  fof(f441,plain,(
% 0.21/0.53    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(resolution,[],[f440,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f440,plain,(
% 0.21/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f439,f342])).
% 0.21/0.53  fof(f439,plain,(
% 0.21/0.53    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f438,f144])).
% 0.21/0.53  fof(f438,plain,(
% 0.21/0.53    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f114,f151])).
% 0.21/0.53  fof(f425,plain,(
% 0.21/0.53    spl4_1 | ~spl4_4 | ~spl4_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f422])).
% 0.21/0.53  fof(f422,plain,(
% 0.21/0.53    $false | (spl4_1 | ~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f305,f367])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl4_1 | ~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(backward_demodulation,[],[f307,f342])).
% 0.21/0.53  fof(f307,plain,(
% 0.21/0.53    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_1 | ~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(backward_demodulation,[],[f273,f144])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_1 | ~spl4_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f266,f63])).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_6)),
% 0.21/0.54    inference(backward_demodulation,[],[f110,f151])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    spl4_1 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    spl4_1 | spl4_6),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f245])).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    $false | (spl4_1 | spl4_6)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f110,f172])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_6),
% 0.21/0.54    inference(backward_demodulation,[],[f90,f168])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK2) | spl4_6),
% 0.21/0.54    inference(backward_demodulation,[],[f71,f166])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | spl4_6),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f35,f36,f152,f57])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.54    inference(forward_demodulation,[],[f89,f84])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))),
% 0.21/0.54    inference(forward_demodulation,[],[f86,f77])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f78,f79,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    spl4_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    $false | spl4_5),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f36,f148,f49])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    spl4_5 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    spl4_4 | ~spl4_5 | ~spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f97,f150,f146,f142])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(superposition,[],[f47,f74])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f116,f112,f108])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (18397)------------------------------
% 0.21/0.54  % (18397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18397)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (18397)Memory used [KB]: 6780
% 0.21/0.54  % (18397)Time elapsed: 0.105 s
% 0.21/0.54  % (18397)------------------------------
% 0.21/0.54  % (18397)------------------------------
% 0.21/0.54  % (18404)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (18403)Refutation not found, incomplete strategy% (18403)------------------------------
% 0.21/0.54  % (18403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18401)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (18403)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18403)Memory used [KB]: 10618
% 0.21/0.54  % (18403)Time elapsed: 0.117 s
% 0.21/0.54  % (18403)------------------------------
% 0.21/0.54  % (18403)------------------------------
% 0.21/0.54  % (18401)Refutation not found, incomplete strategy% (18401)------------------------------
% 0.21/0.54  % (18401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18401)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18401)Memory used [KB]: 10746
% 0.21/0.54  % (18401)Time elapsed: 0.139 s
% 0.21/0.54  % (18401)------------------------------
% 0.21/0.54  % (18401)------------------------------
% 0.21/0.54  % (18395)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (18407)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (18409)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (18392)Success in time 0.183 s
%------------------------------------------------------------------------------
