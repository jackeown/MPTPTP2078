%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 202 expanded)
%              Number of leaves         :   15 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  243 ( 682 expanded)
%              Number of equality atoms :   69 ( 230 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f82,f89,f113,f297,f320,f418])).

fof(f418,plain,
    ( ~ spl1_3
    | ~ spl1_4
    | spl1_18 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl1_3
    | ~ spl1_4
    | spl1_18 ),
    inference(subsumption_resolution,[],[f416,f255])).

fof(f255,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f200,f145])).

fof(f145,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_4 ),
    inference(resolution,[],[f119,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f119,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f114,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f114,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))
    | ~ spl1_4 ),
    inference(backward_demodulation,[],[f79,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f79,plain,(
    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f200,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f199,f60])).

fof(f199,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f72,f88])).

fof(f72,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl1_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f416,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl1_18 ),
    inference(forward_demodulation,[],[f415,f60])).

fof(f415,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl1_18 ),
    inference(subsumption_resolution,[],[f408,f49])).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f408,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl1_18 ),
    inference(superposition,[],[f296,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f296,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_18 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl1_18
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f320,plain,
    ( ~ spl1_3
    | ~ spl1_4
    | spl1_9 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | ~ spl1_3
    | ~ spl1_4
    | spl1_9 ),
    inference(subsumption_resolution,[],[f141,f255])).

fof(f141,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl1_9
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f297,plain,
    ( ~ spl1_18
    | ~ spl1_9
    | spl1_2
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f292,f86,f67,f139,f294])).

fof(f67,plain,
    ( spl1_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f292,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_2
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f282,f60])).

fof(f282,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl1_2
    | ~ spl1_4 ),
    inference(resolution,[],[f210,f58])).

fof(f58,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f210,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_2
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f206,f49])).

fof(f206,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl1_2
    | ~ spl1_4 ),
    inference(backward_demodulation,[],[f115,f145])).

fof(f115,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_2
    | ~ spl1_4 ),
    inference(backward_demodulation,[],[f69,f88])).

fof(f69,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f113,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f95,f73])).

fof(f73,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f95,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f89,plain,
    ( ~ spl1_3
    | spl1_4
    | spl1_2 ),
    inference(avatar_split_clause,[],[f84,f67,f86,f71])).

fof(f84,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_2 ),
    inference(subsumption_resolution,[],[f83,f39])).

fof(f83,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_2 ),
    inference(resolution,[],[f69,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f81])).

% (25901)Refutation not found, incomplete strategy% (25901)------------------------------
% (25901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25901)Termination reason: Refutation not found, incomplete strategy

% (25901)Memory used [KB]: 6268
% (25901)Time elapsed: 0.053 s
% (25901)------------------------------
% (25901)------------------------------
fof(f81,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,
    ( ~ v1_funct_1(sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl1_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f74,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f32,f71,f67,f63])).

fof(f32,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:06:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (25920)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.46  % (25902)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (25920)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (25913)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (25908)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (25902)Refutation not found, incomplete strategy% (25902)------------------------------
% 0.21/0.47  % (25902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25902)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (25902)Memory used [KB]: 10618
% 0.21/0.47  % (25902)Time elapsed: 0.052 s
% 0.21/0.47  % (25902)------------------------------
% 0.21/0.47  % (25902)------------------------------
% 0.21/0.47  % (25901)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (25913)Refutation not found, incomplete strategy% (25913)------------------------------
% 0.21/0.47  % (25913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (25913)Memory used [KB]: 6140
% 0.21/0.47  % (25913)Time elapsed: 0.056 s
% 0.21/0.47  % (25913)------------------------------
% 0.21/0.47  % (25913)------------------------------
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f419,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f74,f82,f89,f113,f297,f320,f418])).
% 0.21/0.47  fof(f418,plain,(
% 0.21/0.47    ~spl1_3 | ~spl1_4 | spl1_18),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f417])).
% 0.21/0.47  fof(f417,plain,(
% 0.21/0.47    $false | (~spl1_3 | ~spl1_4 | spl1_18)),
% 0.21/0.47    inference(subsumption_resolution,[],[f416,f255])).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl1_3 | ~spl1_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f200,f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl1_4),
% 0.21/0.47    inference(resolution,[],[f119,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    r1_tarski(sK0,k1_xboole_0) | ~spl1_4),
% 0.21/0.47    inference(forward_demodulation,[],[f114,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    inference(flattening,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) | ~spl1_4),
% 0.21/0.47    inference(backward_demodulation,[],[f79,f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl1_4 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.47    inference(resolution,[],[f30,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | (~spl1_3 | ~spl1_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f199,f60])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) | (~spl1_3 | ~spl1_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f72,f88])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl1_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.47  fof(f416,plain,(
% 0.21/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl1_18),
% 0.21/0.47    inference(forward_demodulation,[],[f415,f60])).
% 0.21/0.47  fof(f415,plain,(
% 0.21/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl1_18),
% 0.21/0.47    inference(subsumption_resolution,[],[f408,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.47  fof(f408,plain,(
% 0.21/0.47    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl1_18),
% 0.21/0.47    inference(superposition,[],[f296,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.47  fof(f296,plain,(
% 0.21/0.47    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl1_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f294])).
% 0.21/0.47  fof(f294,plain,(
% 0.21/0.47    spl1_18 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.21/0.47  fof(f320,plain,(
% 0.21/0.47    ~spl1_3 | ~spl1_4 | spl1_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f319])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    $false | (~spl1_3 | ~spl1_4 | spl1_9)),
% 0.21/0.47    inference(subsumption_resolution,[],[f141,f255])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl1_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f139])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    spl1_9 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.47  fof(f297,plain,(
% 0.21/0.47    ~spl1_18 | ~spl1_9 | spl1_2 | ~spl1_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f292,f86,f67,f139,f294])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl1_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.47  fof(f292,plain,(
% 0.21/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl1_2 | ~spl1_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f282,f60])).
% 0.21/0.47  fof(f282,plain,(
% 0.21/0.47    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl1_2 | ~spl1_4)),
% 0.21/0.47    inference(resolution,[],[f210,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.47    inference(equality_resolution,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl1_2 | ~spl1_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f206,f49])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl1_2 | ~spl1_4)),
% 0.21/0.47    inference(backward_demodulation,[],[f115,f145])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl1_2 | ~spl1_4)),
% 0.21/0.47    inference(backward_demodulation,[],[f69,f88])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl1_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    $false | spl1_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f95,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.47    inference(resolution,[],[f79,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ~spl1_3 | spl1_4 | spl1_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f84,f67,f86,f71])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f83,f39])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_2),
% 0.21/0.47    inference(resolution,[],[f69,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl1_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f81])).
% 0.21/0.47  % (25901)Refutation not found, incomplete strategy% (25901)------------------------------
% 0.21/0.47  % (25901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25901)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (25901)Memory used [KB]: 6268
% 0.21/0.47  % (25901)Time elapsed: 0.053 s
% 0.21/0.47  % (25901)------------------------------
% 0.21/0.47  % (25901)------------------------------
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    $false | spl1_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    v1_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~v1_funct_1(sK0) | spl1_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl1_1 <=> v1_funct_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f71,f67,f63])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (25920)------------------------------
% 0.21/0.47  % (25920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25920)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (25920)Memory used [KB]: 6268
% 0.21/0.47  % (25920)Time elapsed: 0.065 s
% 0.21/0.47  % (25920)------------------------------
% 0.21/0.47  % (25920)------------------------------
% 0.21/0.47  % (25916)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (25900)Success in time 0.115 s
%------------------------------------------------------------------------------
