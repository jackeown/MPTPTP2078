%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 153 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  348 ( 573 expanded)
%              Number of equality atoms :   90 ( 147 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f147,f198,f228,f234,f235,f407])).

fof(f407,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f405,f152])).

fof(f152,plain,
    ( v5_relat_1(sK3,k1_tarski(sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_10
  <=> v5_relat_1(sK3,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f405,plain,
    ( ~ v5_relat_1(sK3,k1_tarski(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(equality_resolution,[],[f404])).

fof(f404,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f403,f98])).

fof(f98,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,sK0)
        | sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0)) )
    | spl6_1
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f402,f195])).

fof(f195,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f402,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0))
        | ~ r2_hidden(sK2,k1_relat_1(sK3)) )
    | spl6_1
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f401,f113])).

fof(f113,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f401,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0))
        | ~ r2_hidden(sK2,k1_relat_1(sK3))
        | ~ v1_funct_1(sK3) )
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f389,f146])).

fof(f146,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f389,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v5_relat_1(sK3,k1_tarski(X0))
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK2,k1_relat_1(sK3))
        | ~ v1_funct_1(sK3) )
    | spl6_1 ),
    inference(superposition,[],[f93,f282])).

fof(f282,plain,(
    ! [X10,X8,X9] :
      ( k1_funct_1(X8,X10) = X9
      | ~ v5_relat_1(X8,k1_tarski(X9))
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(X10,k1_relat_1(X8))
      | ~ v1_funct_1(X8) ) ),
    inference(subsumption_resolution,[],[f280,f73])).

fof(f73,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f280,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_funct_1(X8)
      | ~ v5_relat_1(X8,k1_tarski(X9))
      | ~ v1_relat_1(X8)
      | v1_xboole_0(k1_tarski(X9))
      | ~ r2_hidden(X10,k1_relat_1(X8))
      | k1_funct_1(X8,X10) = X9 ) ),
    inference(resolution,[],[f164,f89])).

fof(f89,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),X2)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f68,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f93,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_1
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f235,plain,
    ( spl6_10
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f230,f101,f150])).

fof(f101,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f230,plain,
    ( v5_relat_1(sK3,k1_tarski(sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f103,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f234,plain,
    ( spl6_11
    | spl6_12
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f233,f106,f101,f181,f177])).

fof(f177,plain,
    ( spl6_11
  <=> sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f181,plain,
    ( spl6_12
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f106,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f233,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f229,f108])).

fof(f108,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f229,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f103,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f228,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f204,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f204,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_12 ),
    inference(superposition,[],[f116,f183])).

fof(f183,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f116,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),X0) ),
    inference(resolution,[],[f69,f88])).

fof(f88,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f198,plain,
    ( spl6_13
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f197,f177,f101,f193])).

fof(f197,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f189,f103])).

fof(f189,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_11 ),
    inference(superposition,[],[f61,f179])).

fof(f179,plain,
    ( sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f177])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f147,plain,
    ( spl6_9
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f142,f101,f144])).

fof(f142,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f71,f103])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f42,f111])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f30])).

fof(f30,plain,
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

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f109,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f43,f106])).

fof(f43,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f104,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f44,f101])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f99,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f45,f96])).

fof(f45,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f46,f91])).

fof(f46,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:13:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (18033)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.49  % (18033)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (18025)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f147,f198,f228,f234,f235,f407])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_13),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f406])).
% 0.21/0.51  fof(f406,plain,(
% 0.21/0.51    $false | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f405,f152])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    v5_relat_1(sK3,k1_tarski(sK1)) | ~spl6_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl6_10 <=> v5_relat_1(sK3,k1_tarski(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    ~v5_relat_1(sK3,k1_tarski(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_9 | ~spl6_13)),
% 0.21/0.51    inference(equality_resolution,[],[f404])).
% 0.21/0.51  fof(f404,plain,(
% 0.21/0.51    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_9 | ~spl6_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f403,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    r2_hidden(sK2,sK0) | ~spl6_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl6_2 <=> r2_hidden(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK2,sK0) | sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0))) ) | (spl6_1 | ~spl6_5 | ~spl6_9 | ~spl6_13)),
% 0.21/0.51    inference(forward_demodulation,[],[f402,f195])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | ~spl6_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f193])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    spl6_13 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~r2_hidden(sK2,k1_relat_1(sK3))) ) | (spl6_1 | ~spl6_5 | ~spl6_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f401,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    v1_funct_1(sK3) | ~spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl6_5 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3)) ) | (spl6_1 | ~spl6_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f389,f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    spl6_9 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3)) ) | spl6_1),
% 0.21/0.51    inference(superposition,[],[f93,f282])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (k1_funct_1(X8,X10) = X9 | ~v5_relat_1(X8,k1_tarski(X9)) | ~v1_relat_1(X8) | ~r2_hidden(X10,k1_relat_1(X8)) | ~v1_funct_1(X8)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f280,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    ( ! [X10,X8,X9] : (~v1_funct_1(X8) | ~v5_relat_1(X8,k1_tarski(X9)) | ~v1_relat_1(X8) | v1_xboole_0(k1_tarski(X9)) | ~r2_hidden(X10,k1_relat_1(X8)) | k1_funct_1(X8,X10) = X9) )),
% 0.21/0.51    inference(resolution,[],[f164,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.51    inference(equality_resolution,[],[f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.51    inference(rectify,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X0),X2) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X2) | ~v1_relat_1(X1) | v1_xboole_0(X2) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 0.21/0.51    inference(resolution,[],[f68,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    sK1 != k1_funct_1(sK3,sK2) | spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl6_1 <=> sK1 = k1_funct_1(sK3,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    spl6_10 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f230,f101,f150])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    v5_relat_1(sK3,k1_tarski(sK1)) | ~spl6_3),
% 0.21/0.51    inference(resolution,[],[f103,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    spl6_11 | spl6_12 | ~spl6_3 | ~spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f233,f106,f101,f181,f177])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl6_11 <=> sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    spl6_12 <=> k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl6_4 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | (~spl6_3 | ~spl6_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f229,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | ~spl6_3),
% 0.21/0.51    inference(resolution,[],[f103,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    ~spl6_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f227])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    $false | ~spl6_12),
% 0.21/0.51    inference(subsumption_resolution,[],[f204,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,sK1) | ~spl6_12),
% 0.21/0.51    inference(superposition,[],[f116,f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tarski(sK1) | ~spl6_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f181])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k1_tarski(X0),X0)) )),
% 0.21/0.51    inference(resolution,[],[f69,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.51    inference(equality_resolution,[],[f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.51    inference(equality_resolution,[],[f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    spl6_13 | ~spl6_3 | ~spl6_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f197,f177,f101,f193])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | (~spl6_3 | ~spl6_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f189,f103])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_11),
% 0.21/0.51    inference(superposition,[],[f61,f179])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | ~spl6_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f177])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl6_9 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f142,f101,f144])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl6_3),
% 0.21/0.51    inference(resolution,[],[f71,f103])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f111])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f14])).
% 0.21/0.51  fof(f14,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f106])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f101])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f96])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    r2_hidden(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f91])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    sK1 != k1_funct_1(sK3,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (18033)------------------------------
% 0.21/0.51  % (18033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18033)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (18033)Memory used [KB]: 6524
% 0.21/0.51  % (18033)Time elapsed: 0.078 s
% 0.21/0.51  % (18033)------------------------------
% 0.21/0.51  % (18033)------------------------------
% 0.21/0.51  % (18011)Success in time 0.148 s
%------------------------------------------------------------------------------
