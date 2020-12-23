%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 274 expanded)
%              Number of leaves         :   12 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  255 ( 902 expanded)
%              Number of equality atoms :   61 ( 347 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f118,f151,f190,f246])).

fof(f246,plain,
    ( ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(subsumption_resolution,[],[f235,f244])).

fof(f244,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f243,f42])).

fof(f42,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f243,plain,
    ( ! [X1] : v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1)
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(subsumption_resolution,[],[f242,f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f242,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1) )
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f241,f42])).

fof(f241,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1) )
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(subsumption_resolution,[],[f107,f232])).

fof(f232,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(resolution,[],[f209,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f47,f22])).

fof(f47,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f209,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(backward_demodulation,[],[f170,f204])).

fof(f204,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f203,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f203,plain,
    ( sK0 = k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f146,f168])).

fof(f168,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_1
    | spl1_2 ),
    inference(subsumption_resolution,[],[f167,f56])).

fof(f56,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl1_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f167,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_1 ),
    inference(subsumption_resolution,[],[f163,f139])).

fof(f139,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f51,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl1_1
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f163,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_1 ),
    inference(resolution,[],[f37,f51])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f146,plain,
    ( sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl1_10
  <=> sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f170,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | ~ spl1_1
    | spl1_2 ),
    inference(backward_demodulation,[],[f56,f168])).

fof(f107,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f104,f42])).

fof(f104,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1))
      | ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1) ) ),
    inference(superposition,[],[f59,f83])).

fof(f83,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f72,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f72,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | k1_relset_1(X2,X3,X4) = k1_relat_1(X4) ) ),
    inference(resolution,[],[f32,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f59,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f44,f42])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f235,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_1
    | spl1_2
    | ~ spl1_10 ),
    inference(backward_demodulation,[],[f209,f232])).

fof(f190,plain,
    ( ~ spl1_1
    | spl1_2
    | spl1_11 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl1_1
    | spl1_2
    | spl1_11 ),
    inference(subsumption_resolution,[],[f188,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f27,f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f188,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl1_1
    | spl1_2
    | spl1_11 ),
    inference(forward_demodulation,[],[f177,f41])).

fof(f177,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0),sK0)
    | ~ spl1_1
    | spl1_2
    | spl1_11 ),
    inference(backward_demodulation,[],[f150,f168])).

fof(f150,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | spl1_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl1_11
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f151,plain,
    ( spl1_10
    | ~ spl1_11
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f142,f50,f148,f144])).

fof(f142,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_1 ),
    inference(resolution,[],[f140,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f140,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_1 ),
    inference(resolution,[],[f51,f27])).

fof(f118,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f116,f39])).

fof(f116,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f111,f39])).

fof(f111,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl1_1 ),
    inference(resolution,[],[f110,f52])).

fof(f52,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(sK0),X1)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f57,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f48,f54,f50])).

fof(f48,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f19,f21])).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:09:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (18267)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (18275)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (18275)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f57,f118,f151,f190,f246])).
% 0.20/0.51  fof(f246,plain,(
% 0.20/0.51    ~spl1_1 | spl1_2 | ~spl1_10),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f245])).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    $false | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f235,f244])).
% 0.20/0.51  fof(f244,plain,(
% 0.20/0.51    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) ) | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f243,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f243,plain,(
% 0.20/0.51    ( ! [X1] : (v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1)) ) | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f242,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.51  fof(f242,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1)) ) | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f241,f42])).
% 0.20/0.51  fof(f241,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(k2_zfmisc_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1)) ) | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f107,f232])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(resolution,[],[f209,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f47,f22])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(backward_demodulation,[],[f170,f204])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f203,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    sK0 = k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0) | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f146,f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(sK0) | (~spl1_1 | spl1_2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f167,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl1_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f163,f139])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f51,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl1_1 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(sK0) | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f37,f51])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f144])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    spl1_10 <=> sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (~spl1_1 | spl1_2)),
% 0.20/0.51    inference(backward_demodulation,[],[f56,f168])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k2_zfmisc_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f104,f42])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 != k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1)) | ~m1_subset_1(k2_zfmisc_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1)) )),
% 0.20/0.51    inference(superposition,[],[f59,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(resolution,[],[f72,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | k1_relset_1(X2,X3,X4) = k1_relat_1(X4)) )),
% 0.20/0.51    inference(resolution,[],[f32,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f44,f42])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_1 | spl1_2 | ~spl1_10)),
% 0.20/0.51    inference(backward_demodulation,[],[f209,f232])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    ~spl1_1 | spl1_2 | spl1_11),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f189])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    $false | (~spl1_1 | spl1_2 | spl1_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f188,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f27,f22])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,sK0) | (~spl1_1 | spl1_2 | spl1_11)),
% 0.20/0.51    inference(forward_demodulation,[],[f177,f41])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0),sK0) | (~spl1_1 | spl1_2 | spl1_11)),
% 0.20/0.51    inference(backward_demodulation,[],[f150,f168])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) | spl1_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f148])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    spl1_11 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    spl1_10 | ~spl1_11 | ~spl1_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f142,f50,f148,f144])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) | sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f140,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f51,f27])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl1_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f117])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    $false | spl1_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f116,f39])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | spl1_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f111,f39])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | spl1_1),
% 0.20/0.51    inference(resolution,[],[f110,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f50])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(sK0),X1) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.20/0.51    inference(resolution,[],[f31,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ~spl1_1 | ~spl1_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f54,f50])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.51    inference(subsumption_resolution,[],[f19,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ~v1_funct_1(sK0) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (18275)------------------------------
% 0.20/0.51  % (18275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18275)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (18275)Memory used [KB]: 10746
% 0.20/0.51  % (18275)Time elapsed: 0.081 s
% 0.20/0.51  % (18275)------------------------------
% 0.20/0.51  % (18275)------------------------------
% 0.20/0.51  % (18252)Success in time 0.148 s
%------------------------------------------------------------------------------
