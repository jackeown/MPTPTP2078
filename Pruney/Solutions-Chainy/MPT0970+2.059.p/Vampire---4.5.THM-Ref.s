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
% DateTime   : Thu Dec  3 13:00:57 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 466 expanded)
%              Number of leaves         :   23 ( 141 expanded)
%              Depth                    :   17
%              Number of atoms          :  466 (2235 expanded)
%              Number of equality atoms :  108 ( 598 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f714,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f470,f520,f534,f547,f636,f656,f695,f708])).

fof(f708,plain,
    ( ~ spl5_19
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f707])).

fof(f707,plain,
    ( $false
    | ~ spl5_19
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f701,f48])).

fof(f48,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f701,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ spl5_19
    | ~ spl5_21 ),
    inference(backward_demodulation,[],[f556,f631])).

fof(f631,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f629])).

fof(f629,plain,
    ( spl5_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f556,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f86,f469])).

fof(f469,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f467])).

fof(f467,plain,
    ( spl5_19
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f86,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f46,f85])).

% (18920)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f85,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f46,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f695,plain,
    ( spl5_18
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f694])).

fof(f694,plain,
    ( $false
    | spl5_18
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f669,f678])).

fof(f678,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f671,f657])).

fof(f657,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f548,f635])).

fof(f635,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl5_22
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f548,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f42,f469])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f671,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(resolution,[],[f666,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f666,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f549,f635])).

fof(f549,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f43,f469])).

fof(f669,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl5_18
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f668,f635])).

fof(f668,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f464,f469])).

fof(f464,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl5_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f656,plain,
    ( ~ spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f655,f299,f295])).

fof(f295,plain,
    ( spl5_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f299,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f655,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f41,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f636,plain,
    ( spl5_21
    | spl5_22
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f617,f467,f633,f629])).

fof(f617,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f612,f548])).

fof(f612,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl5_19 ),
    inference(resolution,[],[f549,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f547,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f545,f50])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f545,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_10 ),
    inference(resolution,[],[f540,f43])).

fof(f540,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_10 ),
    inference(resolution,[],[f297,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f297,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f295])).

fof(f534,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f533])).

fof(f533,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f529,f118])).

fof(f118,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_3
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f529,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | spl5_3 ),
    inference(resolution,[],[f527,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f527,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1)
    | spl5_3 ),
    inference(resolution,[],[f523,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f88,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f88,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f87,f85])).

fof(f87,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f62,f43])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f523,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | spl5_3 ),
    inference(resolution,[],[f118,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f520,plain,
    ( ~ spl5_3
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f516,f128])).

fof(f128,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f126,f86])).

fof(f126,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f119,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f119,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f516,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(resolution,[],[f503,f57])).

% (18912)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f503,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f498,f141])).

fof(f141,plain,
    ( r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f139,f130])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f127,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r1_tarski(sK0,X1)
      | r2_hidden(sK3(X0),X1) ) ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f127,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f125,f86])).

fof(f125,plain,
    ( sK1 = k2_relat_1(sK2)
    | r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f119,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_hidden(sK4(X1,X0),X1) ) ),
    inference(resolution,[],[f54,f56])).

fof(f139,plain,
    ( r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)
    | r1_tarski(sK0,sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f134,f57])).

fof(f134,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,X0),sK0)
        | r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f130,f56])).

fof(f498,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(superposition,[],[f488,f131])).

fof(f131,plain,
    ( sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2))))
    | ~ spl5_3 ),
    inference(resolution,[],[f127,f45])).

fof(f45,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f488,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f479,f296])).

fof(f296,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f295])).

fof(f479,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(resolution,[],[f475,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f475,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_11
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f300,f473])).

fof(f473,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f471,f43])).

fof(f471,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_18 ),
    inference(superposition,[],[f465,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f465,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f463])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f299])).

fof(f470,plain,
    ( spl5_18
    | spl5_19 ),
    inference(avatar_split_clause,[],[f461,f467,f463])).

fof(f461,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f460,f42])).

fof(f460,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f63,f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (18922)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (18897)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (18918)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (18905)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (18904)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.52  % (18907)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.52  % (18903)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.52  % (18901)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.52  % (18909)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.52  % (18917)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.52  % (18905)Refutation not found, incomplete strategy% (18905)------------------------------
% 1.25/0.52  % (18905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (18911)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.53  % (18908)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.53  % (18925)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.25/0.53  % (18922)Refutation not found, incomplete strategy% (18922)------------------------------
% 1.25/0.53  % (18922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (18922)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (18922)Memory used [KB]: 10746
% 1.25/0.53  % (18896)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.53  % (18922)Time elapsed: 0.106 s
% 1.25/0.53  % (18922)------------------------------
% 1.25/0.53  % (18922)------------------------------
% 1.25/0.53  % (18906)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.53  % (18905)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (18905)Memory used [KB]: 10746
% 1.25/0.53  % (18905)Time elapsed: 0.107 s
% 1.25/0.53  % (18905)------------------------------
% 1.25/0.53  % (18905)------------------------------
% 1.25/0.53  % (18898)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.54  % (18895)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.54  % (18916)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (18923)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (18900)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.55  % (18897)Refutation found. Thanks to Tanya!
% 1.40/0.55  % SZS status Theorem for theBenchmark
% 1.40/0.55  % (18921)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % (18914)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f714,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(avatar_sat_refutation,[],[f470,f520,f534,f547,f636,f656,f695,f708])).
% 1.40/0.55  fof(f708,plain,(
% 1.40/0.55    ~spl5_19 | ~spl5_21),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f707])).
% 1.40/0.55  fof(f707,plain,(
% 1.40/0.55    $false | (~spl5_19 | ~spl5_21)),
% 1.40/0.55    inference(subsumption_resolution,[],[f701,f48])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.40/0.55    inference(cnf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.40/0.55  fof(f701,plain,(
% 1.40/0.55    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (~spl5_19 | ~spl5_21)),
% 1.40/0.55    inference(backward_demodulation,[],[f556,f631])).
% 1.40/0.55  fof(f631,plain,(
% 1.40/0.55    k1_xboole_0 = sK2 | ~spl5_21),
% 1.40/0.55    inference(avatar_component_clause,[],[f629])).
% 1.40/0.55  fof(f629,plain,(
% 1.40/0.55    spl5_21 <=> k1_xboole_0 = sK2),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.40/0.55  fof(f556,plain,(
% 1.40/0.55    k1_xboole_0 != k2_relat_1(sK2) | ~spl5_19),
% 1.40/0.55    inference(backward_demodulation,[],[f86,f469])).
% 1.40/0.55  fof(f469,plain,(
% 1.40/0.55    k1_xboole_0 = sK1 | ~spl5_19),
% 1.40/0.55    inference(avatar_component_clause,[],[f467])).
% 1.40/0.55  fof(f467,plain,(
% 1.40/0.55    spl5_19 <=> k1_xboole_0 = sK1),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.40/0.55  fof(f86,plain,(
% 1.40/0.55    sK1 != k2_relat_1(sK2)),
% 1.40/0.55    inference(superposition,[],[f46,f85])).
% 1.40/0.55  % (18920)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.55  fof(f85,plain,(
% 1.40/0.55    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.40/0.55    inference(resolution,[],[f60,f43])).
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29])).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f16,plain,(
% 1.40/0.55    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.40/0.55    inference(flattening,[],[f15])).
% 1.40/0.55  fof(f15,plain,(
% 1.40/0.55    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.40/0.55    inference(ennf_transformation,[],[f14])).
% 1.40/0.55  fof(f14,negated_conjecture,(
% 1.40/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.40/0.55    inference(negated_conjecture,[],[f13])).
% 1.40/0.55  fof(f13,conjecture,(
% 1.40/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 1.40/0.55  fof(f60,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(X2) = k2_relset_1(X0,X1,X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f22])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f11])).
% 1.40/0.55  fof(f11,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.40/0.55  fof(f46,plain,(
% 1.40/0.55    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f695,plain,(
% 1.40/0.55    spl5_18 | ~spl5_19 | ~spl5_22),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f694])).
% 1.40/0.55  fof(f694,plain,(
% 1.40/0.55    $false | (spl5_18 | ~spl5_19 | ~spl5_22)),
% 1.40/0.55    inference(subsumption_resolution,[],[f669,f678])).
% 1.40/0.55  fof(f678,plain,(
% 1.40/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl5_19 | ~spl5_22)),
% 1.40/0.55    inference(subsumption_resolution,[],[f671,f657])).
% 1.40/0.55  fof(f657,plain,(
% 1.40/0.55    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl5_19 | ~spl5_22)),
% 1.40/0.55    inference(forward_demodulation,[],[f548,f635])).
% 1.40/0.55  fof(f635,plain,(
% 1.40/0.55    k1_xboole_0 = sK0 | ~spl5_22),
% 1.40/0.55    inference(avatar_component_clause,[],[f633])).
% 1.40/0.55  fof(f633,plain,(
% 1.40/0.55    spl5_22 <=> k1_xboole_0 = sK0),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.40/0.55  fof(f548,plain,(
% 1.40/0.55    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl5_19),
% 1.40/0.55    inference(backward_demodulation,[],[f42,f469])).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f671,plain,(
% 1.40/0.55    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl5_19 | ~spl5_22)),
% 1.40/0.55    inference(resolution,[],[f666,f78])).
% 1.40/0.55  fof(f78,plain,(
% 1.40/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.40/0.55    inference(equality_resolution,[],[f64])).
% 1.40/0.55  fof(f64,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(nnf_transformation,[],[f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(flattening,[],[f25])).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f12])).
% 1.40/0.55  fof(f12,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.40/0.55  fof(f666,plain,(
% 1.40/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_19 | ~spl5_22)),
% 1.40/0.55    inference(forward_demodulation,[],[f549,f635])).
% 1.40/0.55  fof(f549,plain,(
% 1.40/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl5_19),
% 1.40/0.55    inference(backward_demodulation,[],[f43,f469])).
% 1.40/0.55  fof(f669,plain,(
% 1.40/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl5_18 | ~spl5_19 | ~spl5_22)),
% 1.40/0.55    inference(forward_demodulation,[],[f668,f635])).
% 1.40/0.55  fof(f668,plain,(
% 1.40/0.55    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl5_18 | ~spl5_19)),
% 1.40/0.55    inference(forward_demodulation,[],[f464,f469])).
% 1.40/0.55  fof(f464,plain,(
% 1.40/0.55    sK0 != k1_relset_1(sK0,sK1,sK2) | spl5_18),
% 1.40/0.55    inference(avatar_component_clause,[],[f463])).
% 1.40/0.55  fof(f463,plain,(
% 1.40/0.55    spl5_18 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.40/0.55  fof(f656,plain,(
% 1.40/0.55    ~spl5_10 | spl5_11),
% 1.40/0.55    inference(avatar_split_clause,[],[f655,f299,f295])).
% 1.40/0.55  fof(f295,plain,(
% 1.40/0.55    spl5_10 <=> v1_relat_1(sK2)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.40/0.55  fof(f299,plain,(
% 1.40/0.55    spl5_11 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.40/0.55  fof(f655,plain,(
% 1.40/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~v1_relat_1(sK2)) )),
% 1.40/0.55    inference(resolution,[],[f41,f79])).
% 1.40/0.55  fof(f79,plain,(
% 1.40/0.55    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 1.40/0.55    inference(equality_resolution,[],[f71])).
% 1.40/0.55  fof(f71,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f40])).
% 1.40/0.55  fof(f40,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.40/0.55    inference(flattening,[],[f39])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.40/0.55    inference(nnf_transformation,[],[f28])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.40/0.55    inference(flattening,[],[f27])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.40/0.55    inference(ennf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.40/0.55  fof(f41,plain,(
% 1.40/0.55    v1_funct_1(sK2)),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f636,plain,(
% 1.40/0.55    spl5_21 | spl5_22 | ~spl5_19),
% 1.40/0.55    inference(avatar_split_clause,[],[f617,f467,f633,f629])).
% 1.40/0.55  fof(f617,plain,(
% 1.40/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl5_19),
% 1.40/0.55    inference(subsumption_resolution,[],[f612,f548])).
% 1.40/0.55  fof(f612,plain,(
% 1.40/0.55    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl5_19),
% 1.40/0.55    inference(resolution,[],[f549,f76])).
% 1.40/0.55  fof(f76,plain,(
% 1.40/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.40/0.55    inference(equality_resolution,[],[f67])).
% 1.40/0.55  fof(f67,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f38])).
% 1.40/0.55  fof(f547,plain,(
% 1.40/0.55    spl5_10),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f546])).
% 1.40/0.55  fof(f546,plain,(
% 1.40/0.55    $false | spl5_10),
% 1.40/0.55    inference(subsumption_resolution,[],[f545,f50])).
% 1.40/0.55  fof(f50,plain,(
% 1.40/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f5])).
% 1.40/0.55  fof(f5,axiom,(
% 1.40/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.40/0.55  fof(f545,plain,(
% 1.40/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_10),
% 1.40/0.55    inference(resolution,[],[f540,f43])).
% 1.40/0.55  fof(f540,plain,(
% 1.40/0.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_10),
% 1.40/0.55    inference(resolution,[],[f297,f49])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f17])).
% 1.40/0.55  fof(f17,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.40/0.55  fof(f297,plain,(
% 1.40/0.55    ~v1_relat_1(sK2) | spl5_10),
% 1.40/0.55    inference(avatar_component_clause,[],[f295])).
% 1.40/0.55  fof(f534,plain,(
% 1.40/0.55    spl5_3),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f533])).
% 1.40/0.55  fof(f533,plain,(
% 1.40/0.55    $false | spl5_3),
% 1.40/0.55    inference(subsumption_resolution,[],[f529,f118])).
% 1.40/0.55  fof(f118,plain,(
% 1.40/0.55    ~r1_tarski(k2_relat_1(sK2),sK1) | spl5_3),
% 1.40/0.55    inference(avatar_component_clause,[],[f117])).
% 1.40/0.55  fof(f117,plain,(
% 1.40/0.55    spl5_3 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.40/0.55  fof(f529,plain,(
% 1.40/0.55    r1_tarski(k2_relat_1(sK2),sK1) | spl5_3),
% 1.40/0.55    inference(resolution,[],[f527,f57])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f37])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.55    inference(rectify,[],[f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.55    inference(nnf_transformation,[],[f19])).
% 1.40/0.55  fof(f19,plain,(
% 1.40/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.55  fof(f527,plain,(
% 1.40/0.55    r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1) | spl5_3),
% 1.40/0.55    inference(resolution,[],[f523,f89])).
% 1.40/0.55  fof(f89,plain,(
% 1.40/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) )),
% 1.40/0.55    inference(resolution,[],[f88,f51])).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,plain,(
% 1.40/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f3])).
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.40/0.55  fof(f88,plain,(
% 1.40/0.55    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.40/0.55    inference(forward_demodulation,[],[f87,f85])).
% 1.40/0.55  fof(f87,plain,(
% 1.40/0.55    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 1.40/0.55    inference(resolution,[],[f62,f43])).
% 1.40/0.55  fof(f62,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f24])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f9])).
% 1.40/0.55  fof(f9,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.40/0.55  fof(f523,plain,(
% 1.40/0.55    r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | spl5_3),
% 1.40/0.55    inference(resolution,[],[f118,f56])).
% 1.40/0.55  fof(f56,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f37])).
% 1.40/0.55  fof(f520,plain,(
% 1.40/0.55    ~spl5_3 | ~spl5_10 | ~spl5_11 | ~spl5_18),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f519])).
% 1.40/0.55  fof(f519,plain,(
% 1.40/0.55    $false | (~spl5_3 | ~spl5_10 | ~spl5_11 | ~spl5_18)),
% 1.40/0.55    inference(subsumption_resolution,[],[f516,f128])).
% 1.40/0.55  fof(f128,plain,(
% 1.40/0.55    ~r1_tarski(sK1,k2_relat_1(sK2)) | ~spl5_3),
% 1.40/0.55    inference(subsumption_resolution,[],[f126,f86])).
% 1.40/0.55  fof(f126,plain,(
% 1.40/0.55    sK1 = k2_relat_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2)) | ~spl5_3),
% 1.40/0.55    inference(resolution,[],[f119,f54])).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f33,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(flattening,[],[f32])).
% 1.40/0.55  fof(f32,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f2])).
% 1.40/0.55  fof(f2,axiom,(
% 1.40/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.55  fof(f119,plain,(
% 1.40/0.55    r1_tarski(k2_relat_1(sK2),sK1) | ~spl5_3),
% 1.40/0.55    inference(avatar_component_clause,[],[f117])).
% 1.40/0.55  fof(f516,plain,(
% 1.40/0.55    r1_tarski(sK1,k2_relat_1(sK2)) | (~spl5_3 | ~spl5_10 | ~spl5_11 | ~spl5_18)),
% 1.40/0.55    inference(resolution,[],[f503,f57])).
% 1.40/0.55  % (18912)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.55  fof(f503,plain,(
% 1.40/0.55    r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | (~spl5_3 | ~spl5_10 | ~spl5_11 | ~spl5_18)),
% 1.40/0.55    inference(subsumption_resolution,[],[f498,f141])).
% 1.40/0.55  fof(f141,plain,(
% 1.40/0.55    r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) | ~spl5_3),
% 1.40/0.55    inference(subsumption_resolution,[],[f139,f130])).
% 1.40/0.55  fof(f130,plain,(
% 1.40/0.55    ( ! [X0] : (~r1_tarski(sK0,X0) | r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),X0)) ) | ~spl5_3),
% 1.40/0.55    inference(resolution,[],[f127,f82])).
% 1.40/0.55  fof(f82,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~r1_tarski(sK0,X1) | r2_hidden(sK3(X0),X1)) )),
% 1.40/0.55    inference(resolution,[],[f55,f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f55,plain,(
% 1.40/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f37])).
% 1.40/0.55  fof(f127,plain,(
% 1.40/0.55    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | ~spl5_3),
% 1.40/0.55    inference(subsumption_resolution,[],[f125,f86])).
% 1.40/0.55  fof(f125,plain,(
% 1.40/0.55    sK1 = k2_relat_1(sK2) | r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | ~spl5_3),
% 1.40/0.55    inference(resolution,[],[f119,f81])).
% 1.40/0.55  fof(f81,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_hidden(sK4(X1,X0),X1)) )),
% 1.40/0.55    inference(resolution,[],[f54,f56])).
% 1.40/0.55  fof(f139,plain,(
% 1.40/0.55    r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) | r1_tarski(sK0,sK0) | ~spl5_3),
% 1.40/0.55    inference(resolution,[],[f134,f57])).
% 1.40/0.55  fof(f134,plain,(
% 1.40/0.55    ( ! [X0] : (r2_hidden(sK4(sK0,X0),sK0) | r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),X0)) ) | ~spl5_3),
% 1.40/0.55    inference(resolution,[],[f130,f56])).
% 1.40/0.55  fof(f498,plain,(
% 1.40/0.55    r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) | (~spl5_3 | ~spl5_10 | ~spl5_11 | ~spl5_18)),
% 1.40/0.55    inference(superposition,[],[f488,f131])).
% 1.40/0.55  fof(f131,plain,(
% 1.40/0.55    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2)))) | ~spl5_3),
% 1.40/0.55    inference(resolution,[],[f127,f45])).
% 1.40/0.55  fof(f45,plain,(
% 1.40/0.55    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f488,plain,(
% 1.40/0.55    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2)) | ~r2_hidden(X1,sK0)) ) | (~spl5_10 | ~spl5_11 | ~spl5_18)),
% 1.40/0.55    inference(subsumption_resolution,[],[f479,f296])).
% 1.40/0.55  fof(f296,plain,(
% 1.40/0.55    v1_relat_1(sK2) | ~spl5_10),
% 1.40/0.55    inference(avatar_component_clause,[],[f295])).
% 1.40/0.55  fof(f479,plain,(
% 1.40/0.55    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | (~spl5_11 | ~spl5_18)),
% 1.40/0.55    inference(resolution,[],[f475,f59])).
% 1.40/0.55  fof(f59,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f21])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.40/0.55    inference(flattening,[],[f20])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.40/0.55    inference(ennf_transformation,[],[f6])).
% 1.40/0.55  fof(f6,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 1.40/0.55  fof(f475,plain,(
% 1.40/0.55    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~r2_hidden(X0,sK0)) ) | (~spl5_11 | ~spl5_18)),
% 1.40/0.55    inference(backward_demodulation,[],[f300,f473])).
% 1.40/0.55  fof(f473,plain,(
% 1.40/0.55    sK0 = k1_relat_1(sK2) | ~spl5_18),
% 1.40/0.55    inference(subsumption_resolution,[],[f471,f43])).
% 1.40/0.55  fof(f471,plain,(
% 1.40/0.55    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_18),
% 1.40/0.55    inference(superposition,[],[f465,f61])).
% 1.40/0.55  fof(f61,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f23])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.40/0.55  fof(f465,plain,(
% 1.40/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_18),
% 1.40/0.55    inference(avatar_component_clause,[],[f463])).
% 1.40/0.55  fof(f300,plain,(
% 1.40/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)) ) | ~spl5_11),
% 1.40/0.55    inference(avatar_component_clause,[],[f299])).
% 1.40/0.55  fof(f470,plain,(
% 1.40/0.55    spl5_18 | spl5_19),
% 1.40/0.55    inference(avatar_split_clause,[],[f461,f467,f463])).
% 1.40/0.55  fof(f461,plain,(
% 1.40/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f460,f42])).
% 1.40/0.55  fof(f460,plain,(
% 1.40/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.40/0.55    inference(resolution,[],[f63,f43])).
% 1.40/0.55  fof(f63,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.40/0.55    inference(cnf_transformation,[],[f38])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (18897)------------------------------
% 1.40/0.55  % (18897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (18897)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (18897)Memory used [KB]: 11001
% 1.40/0.55  % (18897)Time elapsed: 0.126 s
% 1.40/0.55  % (18897)------------------------------
% 1.40/0.55  % (18897)------------------------------
% 1.40/0.55  % (18924)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.56  % (18912)Refutation not found, incomplete strategy% (18912)------------------------------
% 1.40/0.56  % (18912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (18912)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (18912)Memory used [KB]: 10746
% 1.40/0.56  % (18912)Time elapsed: 0.151 s
% 1.40/0.56  % (18912)------------------------------
% 1.40/0.56  % (18912)------------------------------
% 1.40/0.56  % (18915)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.56  % (18891)Success in time 0.197 s
%------------------------------------------------------------------------------
