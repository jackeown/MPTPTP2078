%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 122 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  250 ( 304 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f71,f132,f135,f139,f167,f173,f179,f185,f187])).

fof(f187,plain,(
    ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl5_10 ),
    inference(resolution,[],[f157,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f157,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl5_10
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f185,plain,
    ( ~ spl5_2
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl5_2
    | spl5_13 ),
    inference(subsumption_resolution,[],[f60,f183])).

fof(f183,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | spl5_13 ),
    inference(resolution,[],[f178,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f49,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

% (8250)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f178,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl5_13
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f60,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f179,plain,
    ( ~ spl5_13
    | spl5_10
    | spl5_12 ),
    inference(avatar_split_clause,[],[f175,f171,f156,f177])).

fof(f171,plain,
    ( spl5_12
  <=> r2_hidden(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f175,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl5_12 ),
    inference(resolution,[],[f172,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f172,plain,
    ( ~ r2_hidden(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f173,plain,
    ( ~ spl5_12
    | spl5_11 ),
    inference(avatar_split_clause,[],[f169,f165,f171])).

fof(f165,plain,
    ( spl5_11
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f169,plain,
    ( ~ r2_hidden(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl5_11 ),
    inference(resolution,[],[f166,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f166,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( ~ spl5_4
    | ~ spl5_11
    | spl5_6 ),
    inference(avatar_split_clause,[],[f161,f130,f165,f124])).

fof(f124,plain,
    ( spl5_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f130,plain,
    ( spl5_6
  <=> r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f161,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | spl5_6 ),
    inference(resolution,[],[f144,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl5_6 ),
    inference(resolution,[],[f131,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f131,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f139,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f136,f127,f124])).

fof(f127,plain,
    ( spl5_5
  <=> r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f136,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_5 ),
    inference(resolution,[],[f128,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f128,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f135,plain,
    ( ~ spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f60,f133])).

fof(f133,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_4 ),
    inference(resolution,[],[f125,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f125,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f132,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_3 ),
    inference(avatar_split_clause,[],[f122,f69,f130,f127,f124])).

fof(f69,plain,
    ( spl5_3
  <=> m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f122,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2)
    | ~ r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1)
    | ~ v1_relat_1(sK3)
    | spl5_3 ),
    inference(resolution,[],[f77,f70])).

fof(f70,plain,
    ( ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X3)
      | ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f71,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f66,f55,f69,f59])).

fof(f55,plain,
    ( spl5_1
  <=> m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f66,plain,
    ( ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl5_1 ),
    inference(superposition,[],[f56,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f56,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f61,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

fof(f57,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f36,f55])).

fof(f36,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:08:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (8253)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (8261)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (8253)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f188,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f57,f61,f71,f132,f135,f139,f167,f173,f179,f185,f187])).
% 0.20/0.46  fof(f187,plain,(
% 0.20/0.46    ~spl5_10),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f186])).
% 0.20/0.46  fof(f186,plain,(
% 0.20/0.46    $false | ~spl5_10),
% 0.20/0.46    inference(resolution,[],[f157,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.46  fof(f157,plain,(
% 0.20/0.46    v1_xboole_0(k1_zfmisc_1(sK2)) | ~spl5_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f156])).
% 0.20/0.46  fof(f156,plain,(
% 0.20/0.46    spl5_10 <=> v1_xboole_0(k1_zfmisc_1(sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.46  fof(f185,plain,(
% 0.20/0.46    ~spl5_2 | spl5_13),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f184])).
% 0.20/0.46  fof(f184,plain,(
% 0.20/0.46    $false | (~spl5_2 | spl5_13)),
% 0.20/0.46    inference(subsumption_resolution,[],[f60,f183])).
% 0.20/0.46  fof(f183,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | spl5_13),
% 0.20/0.46    inference(resolution,[],[f178,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.46    inference(superposition,[],[f49,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.46  % (8250)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) | spl5_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f177])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    spl5_13 <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    ~spl5_13 | spl5_10 | spl5_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f175,f171,f156,f177])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    spl5_12 <=> r2_hidden(k1_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    v1_xboole_0(k1_zfmisc_1(sK2)) | ~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) | spl5_12),
% 0.20/0.47    inference(resolution,[],[f172,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ~r2_hidden(k1_relat_1(sK3),k1_zfmisc_1(sK2)) | spl5_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f171])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    ~spl5_12 | spl5_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f169,f165,f171])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl5_11 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    ~r2_hidden(k1_relat_1(sK3),k1_zfmisc_1(sK2)) | spl5_11),
% 0.20/0.47    inference(resolution,[],[f166,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(equality_resolution,[],[f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.47    inference(rectify,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    ~r1_tarski(k1_relat_1(sK3),sK2) | spl5_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f165])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ~spl5_4 | ~spl5_11 | spl5_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f161,f130,f165,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl5_4 <=> v1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    spl5_6 <=> r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | spl5_6),
% 0.20/0.47    inference(resolution,[],[f144,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),X0) | ~r1_tarski(X0,sK2)) ) | spl5_6),
% 0.20/0.47    inference(resolution,[],[f131,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    ~r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2) | spl5_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f130])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ~spl5_4 | spl5_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f136,f127,f124])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    spl5_5 <=> r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ~v1_relat_1(sK3) | spl5_5),
% 0.20/0.47    inference(resolution,[],[f128,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ~r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) | spl5_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f127])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    ~spl5_2 | spl5_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f134])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    $false | (~spl5_2 | spl5_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f60,f133])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_4),
% 0.20/0.47    inference(resolution,[],[f125,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ~v1_relat_1(sK3) | spl5_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f122,f69,f130,f127,f124])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl5_3 <=> m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    ~r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2) | ~r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) | ~v1_relat_1(sK3) | spl5_3),
% 0.20/0.47    inference(resolution,[],[f77,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f69])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),X3) | ~r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X2) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(resolution,[],[f46,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ~spl5_2 | ~spl5_3 | spl5_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f66,f55,f69,f59])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl5_1 <=> m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | spl5_1),
% 0.20/0.47    inference(superposition,[],[f56,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f59])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f13])).
% 0.20/0.47  fof(f13,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ~spl5_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f55])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (8253)------------------------------
% 0.20/0.47  % (8253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (8253)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (8253)Memory used [KB]: 10746
% 0.20/0.47  % (8253)Time elapsed: 0.059 s
% 0.20/0.47  % (8253)------------------------------
% 0.20/0.47  % (8253)------------------------------
% 0.20/0.47  % (8243)Success in time 0.12 s
%------------------------------------------------------------------------------
