%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:56 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 180 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  191 ( 447 expanded)
%              Number of equality atoms :   61 ( 153 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f144,f151,f185])).

fof(f185,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f50,f180,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f180,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_6 ),
    inference(superposition,[],[f68,f135])).

fof(f135,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_6
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f68,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f151,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f30,f146])).

fof(f146,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f96,f139])).

fof(f139,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_7
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f96,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f87,f27,f94,f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f94,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f87,f78,f85,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f85,plain,(
    v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f29,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f78,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f31,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f31,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f57,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f30,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f144,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f58,f131])).

fof(f131,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f58,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f28,f56])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f140,plain,
    ( ~ spl5_5
    | spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f93,f137,f133,f129])).

fof(f93,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f92,f86])).

fof(f86,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) ),
    inference(unit_resulting_resolution,[],[f57,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

% (27887)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (27864)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (27881)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f92,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.48/0.55  % (27872)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.55  % (27891)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.56  % (27870)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.48/0.56  % (27883)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.59/0.56  % (27895)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.59/0.57  % (27895)Refutation not found, incomplete strategy% (27895)------------------------------
% 1.59/0.57  % (27895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (27895)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (27895)Memory used [KB]: 1663
% 1.59/0.57  % (27895)Time elapsed: 0.145 s
% 1.59/0.57  % (27895)------------------------------
% 1.59/0.57  % (27895)------------------------------
% 1.59/0.57  % (27875)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.59/0.57  % (27890)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.59/0.57  % (27867)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.59/0.57  % (27866)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.59/0.57  % (27891)Refutation found. Thanks to Tanya!
% 1.59/0.57  % SZS status Theorem for theBenchmark
% 1.59/0.57  % SZS output start Proof for theBenchmark
% 1.59/0.57  fof(f186,plain,(
% 1.59/0.57    $false),
% 1.59/0.57    inference(avatar_sat_refutation,[],[f140,f144,f151,f185])).
% 1.59/0.57  fof(f185,plain,(
% 1.59/0.57    ~spl5_6),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f184])).
% 1.59/0.57  fof(f184,plain,(
% 1.59/0.57    $false | ~spl5_6),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f50,f180,f54])).
% 1.59/0.57  fof(f54,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f26])).
% 1.59/0.57  fof(f26,plain,(
% 1.59/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f8])).
% 1.59/0.57  fof(f8,axiom,(
% 1.59/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.59/0.57  fof(f180,plain,(
% 1.59/0.57    r2_hidden(sK1,k1_xboole_0) | ~spl5_6),
% 1.59/0.57    inference(superposition,[],[f68,f135])).
% 1.59/0.57  fof(f135,plain,(
% 1.59/0.57    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl5_6),
% 1.59/0.57    inference(avatar_component_clause,[],[f133])).
% 1.59/0.57  fof(f133,plain,(
% 1.59/0.57    spl5_6 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.59/0.57  fof(f68,plain,(
% 1.59/0.57    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 1.59/0.57    inference(equality_resolution,[],[f67])).
% 1.59/0.57  fof(f67,plain,(
% 1.59/0.57    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 1.59/0.57    inference(equality_resolution,[],[f60])).
% 1.59/0.57  fof(f60,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.59/0.57    inference(definition_unfolding,[],[f37,f55])).
% 1.59/0.57  fof(f55,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.59/0.57    inference(definition_unfolding,[],[f49,f53])).
% 1.59/0.57  fof(f53,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f5])).
% 1.59/0.57  fof(f5,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.57  fof(f49,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f4])).
% 1.59/0.57  fof(f4,axiom,(
% 1.59/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.57  fof(f37,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.59/0.57    inference(cnf_transformation,[],[f2])).
% 1.59/0.57  fof(f2,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.59/0.57  fof(f50,plain,(
% 1.59/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f1])).
% 1.59/0.57  fof(f1,axiom,(
% 1.59/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.59/0.57  fof(f151,plain,(
% 1.59/0.57    ~spl5_7),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f148])).
% 1.59/0.57  fof(f148,plain,(
% 1.59/0.57    $false | ~spl5_7),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f30,f146])).
% 1.59/0.57  fof(f146,plain,(
% 1.59/0.57    ~r2_hidden(sK2,sK0) | ~spl5_7),
% 1.59/0.57    inference(backward_demodulation,[],[f96,f139])).
% 1.59/0.57  fof(f139,plain,(
% 1.59/0.57    sK0 = k1_relat_1(sK3) | ~spl5_7),
% 1.59/0.57    inference(avatar_component_clause,[],[f137])).
% 1.59/0.57  fof(f137,plain,(
% 1.59/0.57    spl5_7 <=> sK0 = k1_relat_1(sK3)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.59/0.57  fof(f96,plain,(
% 1.59/0.57    ~r2_hidden(sK2,k1_relat_1(sK3))),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f87,f27,f94,f32])).
% 1.59/0.57  fof(f32,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f18])).
% 1.59/0.57  fof(f18,plain,(
% 1.59/0.57    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(flattening,[],[f17])).
% 1.59/0.57  fof(f17,plain,(
% 1.59/0.57    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.59/0.57    inference(ennf_transformation,[],[f7])).
% 1.59/0.57  fof(f7,axiom,(
% 1.59/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 1.59/0.57  fof(f94,plain,(
% 1.59/0.57    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f87,f78,f85,f47])).
% 1.59/0.57  fof(f47,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f23])).
% 1.59/0.57  fof(f23,plain,(
% 1.59/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(flattening,[],[f22])).
% 1.59/0.57  fof(f22,plain,(
% 1.59/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.59/0.57    inference(ennf_transformation,[],[f6])).
% 1.59/0.57  fof(f6,axiom,(
% 1.59/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 1.59/0.57  fof(f85,plain,(
% 1.59/0.57    v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f57,f52])).
% 1.59/0.57  fof(f52,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f25])).
% 1.59/0.57  fof(f25,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(ennf_transformation,[],[f10])).
% 1.59/0.57  fof(f10,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.59/0.57  fof(f57,plain,(
% 1.59/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.59/0.57    inference(definition_unfolding,[],[f29,f56])).
% 1.59/0.57  fof(f56,plain,(
% 1.59/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.59/0.57    inference(definition_unfolding,[],[f46,f55])).
% 1.59/0.57  fof(f46,plain,(
% 1.59/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f3])).
% 1.59/0.57  fof(f3,axiom,(
% 1.59/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.57  fof(f29,plain,(
% 1.59/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.59/0.57    inference(cnf_transformation,[],[f16])).
% 1.59/0.57  fof(f16,plain,(
% 1.59/0.57    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.59/0.57    inference(flattening,[],[f15])).
% 1.59/0.57  fof(f15,plain,(
% 1.59/0.57    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.59/0.57    inference(ennf_transformation,[],[f14])).
% 1.59/0.57  fof(f14,negated_conjecture,(
% 1.59/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.59/0.57    inference(negated_conjecture,[],[f13])).
% 1.59/0.57  fof(f13,conjecture,(
% 1.59/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.59/0.57  fof(f78,plain,(
% 1.59/0.57    ~r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f31,f31,f69])).
% 1.59/0.57  fof(f69,plain,(
% 1.59/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.59/0.57    inference(equality_resolution,[],[f61])).
% 1.59/0.57  fof(f61,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.59/0.57    inference(definition_unfolding,[],[f36,f55])).
% 1.59/0.57  fof(f36,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.59/0.57    inference(cnf_transformation,[],[f2])).
% 1.59/0.57  fof(f31,plain,(
% 1.59/0.57    sK1 != k1_funct_1(sK3,sK2)),
% 1.59/0.57    inference(cnf_transformation,[],[f16])).
% 1.59/0.57  fof(f27,plain,(
% 1.59/0.57    v1_funct_1(sK3)),
% 1.59/0.57    inference(cnf_transformation,[],[f16])).
% 1.59/0.57  fof(f87,plain,(
% 1.59/0.57    v1_relat_1(sK3)),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f57,f39])).
% 1.59/0.57  fof(f39,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f19])).
% 1.59/0.57  fof(f19,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(ennf_transformation,[],[f9])).
% 1.59/0.57  fof(f9,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.59/0.57  fof(f30,plain,(
% 1.59/0.57    r2_hidden(sK2,sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f16])).
% 1.59/0.57  fof(f144,plain,(
% 1.59/0.57    spl5_5),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f141])).
% 1.59/0.57  fof(f141,plain,(
% 1.59/0.57    $false | spl5_5),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f58,f131])).
% 1.59/0.57  fof(f131,plain,(
% 1.59/0.57    ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_5),
% 1.59/0.57    inference(avatar_component_clause,[],[f129])).
% 1.59/0.57  fof(f129,plain,(
% 1.59/0.57    spl5_5 <=> v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.59/0.57  fof(f58,plain,(
% 1.59/0.57    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.59/0.57    inference(definition_unfolding,[],[f28,f56])).
% 1.59/0.57  fof(f28,plain,(
% 1.59/0.57    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.59/0.57    inference(cnf_transformation,[],[f16])).
% 1.59/0.57  fof(f140,plain,(
% 1.59/0.57    ~spl5_5 | spl5_6 | spl5_7),
% 1.59/0.57    inference(avatar_split_clause,[],[f93,f137,f133,f129])).
% 1.59/0.57  fof(f93,plain,(
% 1.59/0.57    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.59/0.57    inference(forward_demodulation,[],[f92,f86])).
% 1.59/0.57  fof(f86,plain,(
% 1.59/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f57,f48])).
% 1.59/0.57  fof(f48,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f24])).
% 1.59/0.57  fof(f24,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(ennf_transformation,[],[f11])).
% 1.59/0.57  fof(f11,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.59/0.57  % (27887)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.59/0.57  % (27864)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.59/0.57  % (27881)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.59/0.57  fof(f92,plain,(
% 1.59/0.57    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.59/0.57    inference(resolution,[],[f57,f45])).
% 1.59/0.57  fof(f45,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f21])).
% 1.59/0.57  fof(f21,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(flattening,[],[f20])).
% 1.59/0.57  fof(f20,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.57    inference(ennf_transformation,[],[f12])).
% 1.59/0.57  fof(f12,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.59/0.57  % SZS output end Proof for theBenchmark
% 1.59/0.57  % (27891)------------------------------
% 1.59/0.57  % (27891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (27891)Termination reason: Refutation
% 1.59/0.57  
% 1.59/0.57  % (27891)Memory used [KB]: 6268
% 1.59/0.57  % (27891)Time elapsed: 0.117 s
% 1.59/0.57  % (27891)------------------------------
% 1.59/0.57  % (27891)------------------------------
% 1.59/0.58  % (27892)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.59/0.58  % (27893)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.59/0.58  % (27885)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.59/0.58  % (27858)Success in time 0.223 s
%------------------------------------------------------------------------------
