%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 609 expanded)
%              Number of leaves         :   21 ( 140 expanded)
%              Depth                    :   18
%              Number of atoms          :  335 (1905 expanded)
%              Number of equality atoms :  100 ( 599 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f424,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f101,f125,f194,f316,f341,f423])).

fof(f423,plain,
    ( spl2_2
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | spl2_2
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f414,f311])).

fof(f311,plain,
    ( ! [X3] : v1_funct_2(sK0,k1_xboole_0,X3)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl2_18
  <=> ! [X3] : v1_funct_2(sK0,k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f414,plain,
    ( ~ v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)
    | spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f231,f339])).

fof(f339,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f336,f332])).

fof(f332,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f250,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f43,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f250,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(superposition,[],[f166,f172])).

fof(f172,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f171,f162])).

fof(f162,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f106,f103])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f52,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f106,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_relat_1(X1) ) ),
    inference(superposition,[],[f57,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

% (13513)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f171,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f164,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f164,plain,(
    ! [X1] : v4_relat_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f111,f103])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f59,f68])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f166,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(k1_xboole_0,X0)),X0) ),
    inference(resolution,[],[f162,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f336,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f333,f318])).

fof(f318,plain,
    ( ! [X0] : sK0 = k7_relat_1(sK0,X0)
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f317,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f29])).

fof(f29,plain,
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

fof(f17,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f317,plain,
    ( ! [X0] :
        ( sK0 = k7_relat_1(sK0,X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl2_8 ),
    inference(resolution,[],[f304,f47])).

fof(f304,plain,
    ( ! [X2] : v4_relat_1(sK0,X2)
    | ~ spl2_8 ),
    inference(resolution,[],[f232,f111])).

fof(f232,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f227,f68])).

fof(f227,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ spl2_8 ),
    inference(superposition,[],[f114,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl2_8
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f114,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(resolution,[],[f108,f52])).

fof(f108,plain,(
    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f42,f39])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f333,plain,(
    k1_relat_1(k1_xboole_0) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f250,f110])).

fof(f110,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k7_relat_1(sK0,X1)))
      | k1_relat_1(k7_relat_1(sK0,X1)) = X1 ) ),
    inference(resolution,[],[f50,f104])).

fof(f104,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X0) ),
    inference(resolution,[],[f46,f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f231,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f82,f185])).

fof(f82,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f341,plain,
    ( ~ spl2_8
    | spl2_19 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl2_8
    | spl2_19 ),
    inference(subsumption_resolution,[],[f339,f315])).

fof(f315,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | spl2_19 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl2_19
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f316,plain,
    ( spl2_18
    | ~ spl2_19
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f308,f183,f313,f310])).

fof(f308,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k1_relat_1(sK0)
        | v1_funct_2(sK0,k1_xboole_0,X3) )
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f306,f302])).

fof(f302,plain,
    ( ! [X0] : k1_relat_1(sK0) = k1_relset_1(k1_xboole_0,X0,sK0)
    | ~ spl2_8 ),
    inference(resolution,[],[f232,f133])).

fof(f133,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3) ) ),
    inference(superposition,[],[f58,f69])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f306,plain,
    ( ! [X3] :
        ( v1_funct_2(sK0,k1_xboole_0,X3)
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X3,sK0) )
    | ~ spl2_8 ),
    inference(resolution,[],[f232,f98])).

fof(f98,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f73,f69])).

fof(f73,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f194,plain,
    ( spl2_2
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl2_2
    | spl2_8 ),
    inference(global_subsumption,[],[f181,f177,f184])).

fof(f184,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f183])).

fof(f177,plain,(
    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    inference(resolution,[],[f114,f58])).

fof(f181,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f175,f82])).

fof(f175,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f114,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f125,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f114,f86])).

fof(f86,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f101,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f78,f40])).

fof(f40,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,
    ( ~ v1_funct_1(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f87,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f41,f84,f80,f76])).

fof(f41,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (13511)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.48  % (13511)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (13519)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f87,f101,f125,f194,f316,f341,f423])).
% 0.20/0.50  fof(f423,plain,(
% 0.20/0.50    spl2_2 | ~spl2_8 | ~spl2_18),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f422])).
% 0.20/0.50  fof(f422,plain,(
% 0.20/0.50    $false | (spl2_2 | ~spl2_8 | ~spl2_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f414,f311])).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    ( ! [X3] : (v1_funct_2(sK0,k1_xboole_0,X3)) ) | ~spl2_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f310])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    spl2_18 <=> ! [X3] : v1_funct_2(sK0,k1_xboole_0,X3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.50  fof(f414,plain,(
% 0.20/0.50    ~v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) | (spl2_2 | ~spl2_8)),
% 0.20/0.50    inference(superposition,[],[f231,f339])).
% 0.20/0.50  fof(f339,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK0) | ~spl2_8),
% 0.20/0.50    inference(forward_demodulation,[],[f336,f332])).
% 0.20/0.50  fof(f332,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f250,f102])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,sK1(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(resolution,[],[f43,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.20/0.50  fof(f250,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.20/0.50    inference(superposition,[],[f166,f172])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f171,f162])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    v1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f106,f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(resolution,[],[f52,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(superposition,[],[f57,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  % (13513)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.50    inference(flattening,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.50    inference(resolution,[],[f164,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ( ! [X1] : (v4_relat_1(k1_xboole_0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f111,f103])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 0.20/0.50    inference(superposition,[],[f59,f68])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(k1_xboole_0,X0)),X0)) )),
% 0.20/0.50    inference(resolution,[],[f162,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.50  fof(f336,plain,(
% 0.20/0.50    k1_relat_1(sK0) = k1_relat_1(k1_xboole_0) | ~spl2_8),
% 0.20/0.50    inference(forward_demodulation,[],[f333,f318])).
% 0.20/0.50  fof(f318,plain,(
% 0.20/0.50    ( ! [X0] : (sK0 = k7_relat_1(sK0,X0)) ) | ~spl2_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f317,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    v1_relat_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.50    inference(negated_conjecture,[],[f13])).
% 0.20/0.50  fof(f13,conjecture,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    ( ! [X0] : (sK0 = k7_relat_1(sK0,X0) | ~v1_relat_1(sK0)) ) | ~spl2_8),
% 0.20/0.50    inference(resolution,[],[f304,f47])).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    ( ! [X2] : (v4_relat_1(sK0,X2)) ) | ~spl2_8),
% 0.20/0.50    inference(resolution,[],[f232,f111])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~spl2_8),
% 0.20/0.50    inference(forward_demodulation,[],[f227,f68])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) | ~spl2_8),
% 0.20/0.50    inference(superposition,[],[f114,f185])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK0) | ~spl2_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f183])).
% 0.20/0.50  fof(f183,plain,(
% 0.20/0.50    spl2_8 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.50    inference(resolution,[],[f108,f52])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.20/0.50    inference(resolution,[],[f42,f39])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    k1_relat_1(k1_xboole_0) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(k1_xboole_0)))),
% 0.20/0.50    inference(resolution,[],[f250,f110])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(k7_relat_1(sK0,X1))) | k1_relat_1(k7_relat_1(sK0,X1)) = X1) )),
% 0.20/0.50    inference(resolution,[],[f50,f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X0)) )),
% 0.20/0.50    inference(resolution,[],[f46,f39])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl2_2 | ~spl2_8)),
% 0.20/0.50    inference(superposition,[],[f82,f185])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl2_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl2_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.50  fof(f341,plain,(
% 0.20/0.50    ~spl2_8 | spl2_19),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f340])).
% 0.20/0.50  fof(f340,plain,(
% 0.20/0.50    $false | (~spl2_8 | spl2_19)),
% 0.20/0.50    inference(subsumption_resolution,[],[f339,f315])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    k1_xboole_0 != k1_relat_1(sK0) | spl2_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f313])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    spl2_19 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    spl2_18 | ~spl2_19 | ~spl2_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f308,f183,f313,f310])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    ( ! [X3] : (k1_xboole_0 != k1_relat_1(sK0) | v1_funct_2(sK0,k1_xboole_0,X3)) ) | ~spl2_8),
% 0.20/0.50    inference(forward_demodulation,[],[f306,f302])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(sK0) = k1_relset_1(k1_xboole_0,X0,sK0)) ) | ~spl2_8),
% 0.20/0.50    inference(resolution,[],[f232,f133])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3)) )),
% 0.20/0.50    inference(superposition,[],[f58,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    ( ! [X3] : (v1_funct_2(sK0,k1_xboole_0,X3) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X3,sK0)) ) | ~spl2_8),
% 0.20/0.50    inference(resolution,[],[f232,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f73,f69])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    spl2_2 | spl2_8),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f193])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    $false | (spl2_2 | spl2_8)),
% 0.20/0.50    inference(global_subsumption,[],[f181,f177,f184])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relat_1(sK0) | spl2_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f183])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 0.20/0.50    inference(resolution,[],[f114,f58])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | spl2_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f175,f82])).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f114,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl2_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f124])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    $false | spl2_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f114,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl2_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl2_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl2_1),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    $false | spl2_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    v1_funct_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~v1_funct_1(sK0) | spl2_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl2_1 <=> v1_funct_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ~spl2_1 | ~spl2_2 | ~spl2_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f41,f84,f80,f76])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (13511)------------------------------
% 0.20/0.50  % (13511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13511)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (13511)Memory used [KB]: 10874
% 0.20/0.50  % (13511)Time elapsed: 0.061 s
% 0.20/0.50  % (13511)------------------------------
% 0.20/0.50  % (13511)------------------------------
% 0.20/0.51  % (13500)Success in time 0.142 s
%------------------------------------------------------------------------------
