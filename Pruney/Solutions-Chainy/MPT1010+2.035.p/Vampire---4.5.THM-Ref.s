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
% DateTime   : Thu Dec  3 13:04:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 201 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  332 ( 565 expanded)
%              Number of equality atoms :   92 ( 160 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f611,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f113,f141,f146,f152,f163,f173,f226,f289,f610])).

fof(f610,plain,
    ( ~ spl5_3
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f608,f89])).

fof(f89,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f608,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_15 ),
    inference(superposition,[],[f63,f172])).

fof(f172,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_15
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f63,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f289,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_9
    | spl5_13
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_9
    | spl5_13
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f287,f84])).

fof(f84,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f287,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_9
    | spl5_13
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f286,f201])).

fof(f201,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl5_19
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f286,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_9
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f112,f79,f140,f162,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

% (14240)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (14229)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f162,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl5_13
  <=> m1_subset_1(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f140,plain,
    ( v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_9
  <=> v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f79,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f112,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f226,plain,
    ( spl5_19
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f206,f166,f149,f199])).

fof(f149,plain,
    ( spl5_11
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f166,plain,
    ( spl5_14
  <=> sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f206,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f151,f168])).

fof(f168,plain,
    ( sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f166])).

fof(f151,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f173,plain,
    ( spl5_14
    | spl5_15
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f135,f102,f97,f170,f166])).

fof(f97,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f102,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f135,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f134,f99])).

fof(f99,plain,
    ( v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f134,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f52,f104])).

fof(f104,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

% (14231)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
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

fof(f163,plain,
    ( ~ spl5_13
    | spl5_10 ),
    inference(avatar_split_clause,[],[f147,f143,f160])).

fof(f143,plain,
    ( spl5_10
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f147,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f63,f145,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f145,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f152,plain,
    ( spl5_11
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f122,f102,f149])).

fof(f122,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f104,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f146,plain,
    ( ~ spl5_10
    | spl5_4 ),
    inference(avatar_split_clause,[],[f118,f92,f143])).

fof(f92,plain,
    ( spl5_4
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f118,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f94,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

% (14244)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f94,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f141,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f116,f102,f138])).

fof(f116,plain,
    ( v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f104,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f113,plain,
    ( spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f107,f102,f110])).

fof(f107,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f104,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
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

fof(f105,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f61,f102])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f35,f60])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

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

fof(f100,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f62,f97])).

fof(f62,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f34,f60])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f37,f92])).

fof(f37,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f85,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f36,f82])).

fof(f36,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (14239)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.49  % (14247)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (14230)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (14247)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (14245)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (14245)Refutation not found, incomplete strategy% (14245)------------------------------
% 0.21/0.53  % (14245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14245)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14245)Memory used [KB]: 1791
% 0.21/0.53  % (14245)Time elapsed: 0.107 s
% 0.21/0.53  % (14245)------------------------------
% 0.21/0.53  % (14245)------------------------------
% 0.21/0.53  % (14255)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (14237)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f611,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f113,f141,f146,f152,f163,f173,f226,f289,f610])).
% 0.21/0.53  fof(f610,plain,(
% 0.21/0.53    ~spl5_3 | ~spl5_15),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f609])).
% 0.21/0.53  fof(f609,plain,(
% 0.21/0.53    $false | (~spl5_3 | ~spl5_15)),
% 0.21/0.53    inference(subsumption_resolution,[],[f608,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0) | ~spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl5_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.53  fof(f608,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~spl5_15),
% 0.21/0.53    inference(superposition,[],[f63,f172])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl5_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f170])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    spl5_15 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    ~spl5_1 | ~spl5_2 | ~spl5_7 | ~spl5_9 | spl5_13 | ~spl5_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    $false | (~spl5_1 | ~spl5_2 | ~spl5_7 | ~spl5_9 | spl5_13 | ~spl5_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f287,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    r2_hidden(sK2,sK0) | ~spl5_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl5_2 <=> r2_hidden(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    ~r2_hidden(sK2,sK0) | (~spl5_1 | ~spl5_7 | ~spl5_9 | spl5_13 | ~spl5_19)),
% 0.21/0.53    inference(forward_demodulation,[],[f286,f201])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK3) | ~spl5_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f199])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    spl5_19 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k1_relat_1(sK3)) | (~spl5_1 | ~spl5_7 | ~spl5_9 | spl5_13)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f112,f79,f140,f162,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  % (14240)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (14229)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ~m1_subset_1(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f160])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    spl5_13 <=> m1_subset_1(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl5_9 <=> v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    v1_funct_1(sK3) | ~spl5_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    spl5_1 <=> v1_funct_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~spl5_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl5_7 <=> v1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    spl5_19 | ~spl5_11 | ~spl5_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f206,f166,f149,f199])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    spl5_11 <=> k1_relat_1(sK3) = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    spl5_14 <=> sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK3) | (~spl5_11 | ~spl5_14)),
% 0.21/0.53    inference(backward_demodulation,[],[f151,f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | ~spl5_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f166])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | ~spl5_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f149])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    spl5_14 | spl5_15 | ~spl5_5 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f135,f102,f97,f170,f166])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl5_5 <=> v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl5_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | (~spl5_5 | ~spl5_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f134,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | ~spl5_6),
% 0.21/0.53    inference(resolution,[],[f52,f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f102])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  % (14231)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ~spl5_13 | spl5_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f147,f143,f160])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    spl5_10 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ~m1_subset_1(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_10),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f63,f145,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ~r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f143])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl5_11 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f122,f102,f149])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | ~spl5_6),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f104,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ~spl5_10 | spl5_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f118,f92,f143])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl5_4 <=> sK1 = k1_funct_1(sK3,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ~r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_4),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f94,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 0.21/0.53    inference(equality_resolution,[],[f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f43,f60])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.53  % (14244)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    sK1 != k1_funct_1(sK3,sK2) | spl5_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    spl5_9 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f116,f102,f138])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_6),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f104,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl5_7 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f107,f102,f110])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~spl5_6),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f104,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f61,f102])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 0.21/0.53    inference(definition_unfolding,[],[f35,f60])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f62,f97])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.53    inference(definition_unfolding,[],[f34,f60])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ~spl5_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f92])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    sK1 != k1_funct_1(sK3,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f38,f87])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f82])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    r2_hidden(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f77])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14247)------------------------------
% 0.21/0.53  % (14247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14247)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14247)Memory used [KB]: 11001
% 0.21/0.53  % (14247)Time elapsed: 0.099 s
% 0.21/0.53  % (14247)------------------------------
% 0.21/0.53  % (14247)------------------------------
% 0.21/0.53  % (14226)Success in time 0.166 s
%------------------------------------------------------------------------------
