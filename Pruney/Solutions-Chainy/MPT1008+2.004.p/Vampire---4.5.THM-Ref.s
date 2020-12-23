%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:08 EST 2020

% Result     : Theorem 2.48s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 651 expanded)
%              Number of leaves         :   40 ( 194 expanded)
%              Depth                    :   23
%              Number of atoms          :  735 (1690 expanded)
%              Number of equality atoms :  245 ( 737 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f208,f351,f2002,f2519,f2997,f3234])).

fof(f3234,plain,
    ( ~ spl9_1
    | ~ spl9_60 ),
    inference(avatar_contradiction_clause,[],[f3233])).

fof(f3233,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f3232,f164])).

fof(f164,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3232,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ spl9_1
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f3231,f2518])).

fof(f2518,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f2516])).

fof(f2516,plain,
    ( spl9_60
  <=> k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f3231,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_relat_1(sK4))
    | ~ spl9_1
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f3230,f190])).

fof(f190,plain,
    ( v1_relat_1(sK4)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl9_1
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f3230,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f3229,f79])).

fof(f79,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f60])).

fof(f60,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2))
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f3229,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f3223,f772])).

fof(f772,plain,(
    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4) ),
    inference(forward_demodulation,[],[f145,f630])).

fof(f630,plain,(
    k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f129,f146])).

fof(f146,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f81,f144])).

fof(f144,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f90,f143])).

fof(f143,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f111,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f111,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f90,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f61])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f145,plain,(
    k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) ),
    inference(definition_unfolding,[],[f83,f144,f144])).

fof(f83,plain,(
    k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f3223,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_relat_1(sK4))
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl9_60 ),
    inference(resolution,[],[f3105,f912])).

fof(f912,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k2_enumset1(X0,X0,X0,X0))
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1))
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(extensionality_resolution,[],[f121,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f117,f144,f144])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f3105,plain,
    ( ! [X2,X3] : r1_tarski(k1_relat_1(sK4),k2_enumset1(X2,X2,X3,sK2))
    | ~ spl9_60 ),
    inference(superposition,[],[f172,f2518])).

fof(f172,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f157])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) != X3 ) ),
    inference(definition_unfolding,[],[f138,f127,f144])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_tarski(X2) != X3 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f2997,plain,
    ( ~ spl9_1
    | ~ spl9_5
    | ~ spl9_59 ),
    inference(avatar_contradiction_clause,[],[f2996])).

fof(f2996,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_5
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f2956,f84])).

fof(f84,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f2956,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl9_1
    | ~ spl9_5
    | ~ spl9_59 ),
    inference(superposition,[],[f148,f2950])).

fof(f2950,plain,
    ( o_0_0_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl9_1
    | ~ spl9_5
    | ~ spl9_59 ),
    inference(forward_demodulation,[],[f2949,f458])).

fof(f458,plain,(
    ! [X0] : o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0) ),
    inference(forward_demodulation,[],[f457,f179])).

fof(f179,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f86,f176])).

fof(f176,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f91,f84])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f86,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f457,plain,(
    ! [X0] : k2_relat_1(o_0_0_xboole_0) = k9_relat_1(o_0_0_xboole_0,X0) ),
    inference(forward_demodulation,[],[f378,f392])).

fof(f392,plain,(
    ! [X1] : o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f388,f202])).

fof(f202,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[],[f128,f178])).

fof(f178,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f89,f176])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f388,plain,(
    ! [X1] :
      ( o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X1)
      | ~ v1_relat_1(o_0_0_xboole_0) ) ),
    inference(resolution,[],[f118,f228])).

fof(f228,plain,(
    ! [X0] : v4_relat_1(o_0_0_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f227,f202])).

fof(f227,plain,(
    ! [X0] :
      ( v4_relat_1(o_0_0_xboole_0,X0)
      | ~ v1_relat_1(o_0_0_xboole_0) ) ),
    inference(subsumption_resolution,[],[f225,f181])).

fof(f181,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(backward_demodulation,[],[f88,f176])).

fof(f88,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f225,plain,(
    ! [X0] :
      ( ~ r1_tarski(o_0_0_xboole_0,X0)
      | v4_relat_1(o_0_0_xboole_0,X0)
      | ~ v1_relat_1(o_0_0_xboole_0) ) ),
    inference(superposition,[],[f115,f180])).

fof(f180,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f85,f176])).

fof(f85,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f378,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(o_0_0_xboole_0,X0)) = k9_relat_1(o_0_0_xboole_0,X0) ),
    inference(resolution,[],[f113,f202])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f2949,plain,
    ( ! [X8] : k2_enumset1(sK2,sK2,sK2,sK2) = k9_relat_1(o_0_0_xboole_0,X8)
    | ~ spl9_1
    | ~ spl9_5
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f2946,f353])).

fof(f353,plain,
    ( sP1(o_0_0_xboole_0)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f352,f202])).

fof(f352,plain,
    ( sP1(o_0_0_xboole_0)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl9_5 ),
    inference(resolution,[],[f295,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f39,f58,f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( k1_funct_1(X0,X4) = X3
              & r2_hidden(X4,X1)
              & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP0(X0,X1,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f295,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl9_5
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f2946,plain,
    ( ! [X8] :
        ( k2_enumset1(sK2,sK2,sK2,sK2) = k9_relat_1(o_0_0_xboole_0,X8)
        | ~ sP1(o_0_0_xboole_0) )
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(resolution,[],[f2913,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k9_relat_1(X0,X1) = X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP0(X0,X1,X2) )
          & ( sP0(X0,X1,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f2913,plain,
    ( ! [X8] : sP0(o_0_0_xboole_0,X8,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(resolution,[],[f2794,f833])).

fof(f833,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(o_0_0_xboole_0,X0,X1),X1)
      | sP0(o_0_0_xboole_0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f829,f447])).

fof(f447,plain,(
    ! [X19] : ~ r2_hidden(X19,o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f440,f148])).

fof(f440,plain,(
    ! [X19] :
      ( ~ r2_hidden(X19,o_0_0_xboole_0)
      | v1_xboole_0(k2_enumset1(X19,X19,X19,X19)) ) ),
    inference(resolution,[],[f151,f368])).

fof(f368,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f357,f84])).

fof(f357,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(o_0_0_xboole_0) ) ),
    inference(superposition,[],[f112,f183])).

fof(f183,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f166,f176])).

fof(f166,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f151,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f116,f144])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f829,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(o_0_0_xboole_0,X0,X1),o_0_0_xboole_0)
      | r2_hidden(sK5(o_0_0_xboole_0,X0,X1),X1)
      | sP0(o_0_0_xboole_0,X0,X1) ) ),
    inference(superposition,[],[f102,f180])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
              & r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                & r2_hidden(sK7(X0,X1,X6),X1)
                & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f64,f67,f66,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( k1_funct_1(X0,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X5,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ? [X8] :
                  ( k1_funct_1(X0,X8) = X6
                  & r2_hidden(X8,X1)
                  & r2_hidden(X8,k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f2794,plain,
    ( ! [X3] : ~ r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f2793,f447])).

fof(f2793,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(o_0_0_xboole_0,X3),o_0_0_xboole_0)
        | ~ r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2)) )
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(forward_demodulation,[],[f2759,f179])).

fof(f2759,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(o_0_0_xboole_0,X3),k2_relat_1(o_0_0_xboole_0))
        | ~ r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2)) )
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(backward_demodulation,[],[f888,f2720])).

fof(f2720,plain,
    ( o_0_0_xboole_0 = sK4
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(resolution,[],[f2594,f236])).

fof(f236,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,o_0_0_xboole_0)
      | o_0_0_xboole_0 = X1 ) ),
    inference(resolution,[],[f121,f181])).

fof(f2594,plain,
    ( r1_tarski(sK4,o_0_0_xboole_0)
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(forward_demodulation,[],[f2593,f184])).

fof(f184,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(forward_demodulation,[],[f167,f176])).

fof(f167,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f2593,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(o_0_0_xboole_0,k2_relat_1(sK4)))
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f2592,f79])).

fof(f2592,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(o_0_0_xboole_0,k2_relat_1(sK4)))
    | ~ v1_funct_1(sK4)
    | ~ spl9_1
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f2548,f190])).

fof(f2548,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(o_0_0_xboole_0,k2_relat_1(sK4)))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ spl9_59 ),
    inference(superposition,[],[f581,f2514])).

fof(f2514,plain,
    ( o_0_0_xboole_0 = k1_relat_1(sK4)
    | ~ spl9_59 ),
    inference(avatar_component_clause,[],[f2512])).

fof(f2512,plain,
    ( spl9_59
  <=> o_0_0_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f581,plain,(
    ! [X7] :
      ( r1_tarski(X7,k2_zfmisc_1(k1_relat_1(X7),k2_relat_1(X7)))
      | ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7) ) ),
    inference(resolution,[],[f94,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f888,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2))
      | r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f887,f79])).

fof(f887,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
      | ~ r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2))
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f886,f147])).

fof(f147,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f80,f144])).

fof(f80,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f886,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
      | ~ r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2))
      | ~ v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f885,f146])).

fof(f885,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
      | ~ r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
      | ~ v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f881,f182])).

fof(f182,plain,(
    o_0_0_xboole_0 != sK3 ),
    inference(backward_demodulation,[],[f82,f176])).

fof(f82,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f61])).

fof(f881,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
      | o_0_0_xboole_0 = sK3
      | ~ r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
      | ~ v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
      | ~ v1_funct_1(sK4) ) ),
    inference(superposition,[],[f877,f630])).

fof(f877,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(forward_demodulation,[],[f133,f176])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f148,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f87,f144])).

fof(f87,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f2519,plain,
    ( spl9_59
    | spl9_60
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f2510,f189,f2516,f2512])).

fof(f2510,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | o_0_0_xboole_0 = k1_relat_1(sK4)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f2504,f190])).

fof(f2504,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | o_0_0_xboole_0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(duplicate_literal_removal,[],[f2489])).

fof(f2489,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | o_0_0_xboole_0 = k1_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f974,f255])).

fof(f255,plain,(
    v4_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f130,f146])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f974,plain,(
    ! [X39,X41,X42,X40] :
      ( ~ v4_relat_1(X42,k2_enumset1(X39,X39,X40,X41))
      | k1_relat_1(X42) = k2_enumset1(X39,X39,X39,X41)
      | k1_relat_1(X42) = k2_enumset1(X40,X40,X40,X41)
      | k1_relat_1(X42) = k2_enumset1(X39,X39,X39,X40)
      | k1_relat_1(X42) = k2_enumset1(X41,X41,X41,X41)
      | k1_relat_1(X42) = k2_enumset1(X40,X40,X40,X40)
      | k1_relat_1(X42) = k2_enumset1(X39,X39,X39,X39)
      | o_0_0_xboole_0 = k1_relat_1(X42)
      | k2_enumset1(X39,X39,X40,X41) = k1_relat_1(X42)
      | ~ v1_relat_1(X42) ) ),
    inference(resolution,[],[f949,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f949,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | o_0_0_xboole_0 = X3 ) ),
    inference(forward_demodulation,[],[f161,f176])).

fof(f161,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f134,f127,f143,f143,f143,f144,f144,f144,f127])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2002,plain,(
    ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f2001])).

fof(f2001,plain,
    ( $false
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f1996,f107])).

fof(f107,plain,(
    ! [X0] : v1_relat_1(sK8(X0)) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK8(X0),X2) = X0
          | ~ r2_hidden(X2,k1_tarski(k1_xboole_0)) )
      & k1_tarski(k1_xboole_0) = k1_relat_1(sK8(X0))
      & v1_funct_1(sK8(X0))
      & v1_relat_1(sK8(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = X0
              | ~ r2_hidden(X2,k1_tarski(k1_xboole_0)) )
          & k1_relat_1(X1) = k1_tarski(k1_xboole_0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK8(X0),X2) = X0
            | ~ r2_hidden(X2,k1_tarski(k1_xboole_0)) )
        & k1_tarski(k1_xboole_0) = k1_relat_1(sK8(X0))
        & v1_funct_1(sK8(X0))
        & v1_relat_1(sK8(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = X0
          | ~ r2_hidden(X2,k1_tarski(k1_xboole_0)) )
      & k1_relat_1(X1) = k1_tarski(k1_xboole_0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,k1_tarski(k1_xboole_0))
         => k1_funct_1(X1,X2) = X0 )
      & k1_relat_1(X1) = k1_tarski(k1_xboole_0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e4_61_2__funct_1)).

fof(f1996,plain,
    ( ! [X1] : ~ v1_relat_1(sK8(X1))
    | ~ spl9_7 ),
    inference(resolution,[],[f350,f108])).

fof(f108,plain,(
    ! [X0] : v1_funct_1(sK8(X0)) ),
    inference(cnf_transformation,[],[f70])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl9_7
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f351,plain,
    ( spl9_7
    | spl9_5 ),
    inference(avatar_split_clause,[],[f338,f294,f349])).

fof(f338,plain,(
    ! [X0] :
      ( v1_funct_1(o_0_0_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f95,f178])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f208,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f204,f191])).

fof(f191,plain,
    ( ~ v1_relat_1(sK4)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f189])).

fof(f204,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f128,f146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:13:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (9624)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (9640)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.55  % (9632)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.55  % (9635)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.25/0.55  % (9622)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.56  % (9619)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.56  % (9619)Refutation not found, incomplete strategy% (9619)------------------------------
% 1.25/0.56  % (9619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.56  % (9619)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.56  
% 1.25/0.56  % (9619)Memory used [KB]: 1663
% 1.25/0.56  % (9619)Time elapsed: 0.134 s
% 1.25/0.56  % (9619)------------------------------
% 1.25/0.56  % (9619)------------------------------
% 1.25/0.56  % (9643)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.25/0.56  % (9621)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.25/0.56  % (9620)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.57/0.57  % (9627)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.57/0.57  % (9623)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.57/0.57  % (9626)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.57/0.58  % (9639)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.57/0.58  % (9618)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.57/0.58  % (9631)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.57/0.59  % (9647)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.57/0.59  % (9647)Refutation not found, incomplete strategy% (9647)------------------------------
% 1.57/0.59  % (9647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (9647)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (9647)Memory used [KB]: 1663
% 1.57/0.59  % (9647)Time elapsed: 0.167 s
% 1.57/0.59  % (9647)------------------------------
% 1.57/0.59  % (9647)------------------------------
% 1.57/0.59  % (9628)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.57/0.59  % (9646)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.57/0.59  % (9628)Refutation not found, incomplete strategy% (9628)------------------------------
% 1.57/0.59  % (9628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (9628)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (9628)Memory used [KB]: 10874
% 1.57/0.59  % (9628)Time elapsed: 0.120 s
% 1.57/0.59  % (9628)------------------------------
% 1.57/0.59  % (9628)------------------------------
% 1.57/0.60  % (9633)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.57/0.60  % (9630)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.57/0.60  % (9637)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.57/0.60  % (9636)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.57/0.60  % (9641)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.60  % (9638)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.57/0.61  % (9634)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.61  % (9629)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.57/0.61  % (9642)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.57/0.61  % (9642)Refutation not found, incomplete strategy% (9642)------------------------------
% 1.57/0.61  % (9642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (9642)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.61  
% 1.57/0.61  % (9642)Memory used [KB]: 10746
% 1.57/0.61  % (9642)Time elapsed: 0.143 s
% 1.57/0.61  % (9642)------------------------------
% 1.57/0.61  % (9642)------------------------------
% 1.57/0.61  % (9634)Refutation not found, incomplete strategy% (9634)------------------------------
% 1.57/0.61  % (9634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (9646)Refutation not found, incomplete strategy% (9646)------------------------------
% 1.57/0.61  % (9646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (9646)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.61  
% 1.57/0.61  % (9646)Memory used [KB]: 10874
% 1.57/0.61  % (9646)Time elapsed: 0.185 s
% 1.57/0.61  % (9646)------------------------------
% 1.57/0.61  % (9646)------------------------------
% 1.57/0.61  % (9645)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.57/0.62  % (9634)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.62  
% 1.57/0.62  % (9634)Memory used [KB]: 10746
% 1.57/0.62  % (9634)Time elapsed: 0.180 s
% 1.57/0.62  % (9634)------------------------------
% 1.57/0.62  % (9634)------------------------------
% 1.57/0.62  % (9645)Refutation not found, incomplete strategy% (9645)------------------------------
% 1.57/0.62  % (9645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.62  % (9645)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.62  
% 1.57/0.62  % (9645)Memory used [KB]: 6268
% 1.57/0.62  % (9645)Time elapsed: 0.193 s
% 1.57/0.62  % (9645)------------------------------
% 1.57/0.62  % (9645)------------------------------
% 1.57/0.62  % (9644)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.57/0.62  % (9625)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.62  % (9644)Refutation not found, incomplete strategy% (9644)------------------------------
% 1.57/0.62  % (9644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.62  % (9644)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.62  
% 1.57/0.62  % (9644)Memory used [KB]: 6396
% 1.57/0.62  % (9644)Time elapsed: 0.193 s
% 1.57/0.62  % (9644)------------------------------
% 1.57/0.62  % (9644)------------------------------
% 2.48/0.72  % (9624)Refutation found. Thanks to Tanya!
% 2.48/0.72  % SZS status Theorem for theBenchmark
% 2.48/0.73  % SZS output start Proof for theBenchmark
% 2.48/0.73  fof(f3236,plain,(
% 2.48/0.73    $false),
% 2.48/0.73    inference(avatar_sat_refutation,[],[f208,f351,f2002,f2519,f2997,f3234])).
% 2.48/0.73  fof(f3234,plain,(
% 2.48/0.73    ~spl9_1 | ~spl9_60),
% 2.48/0.73    inference(avatar_contradiction_clause,[],[f3233])).
% 2.48/0.73  fof(f3233,plain,(
% 2.48/0.73    $false | (~spl9_1 | ~spl9_60)),
% 2.48/0.73    inference(subsumption_resolution,[],[f3232,f164])).
% 2.48/0.73  fof(f164,plain,(
% 2.48/0.73    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.48/0.73    inference(equality_resolution,[],[f120])).
% 2.48/0.73  fof(f120,plain,(
% 2.48/0.73    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.48/0.73    inference(cnf_transformation,[],[f73])).
% 2.48/0.73  fof(f73,plain,(
% 2.48/0.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.48/0.73    inference(flattening,[],[f72])).
% 2.48/0.73  fof(f72,plain,(
% 2.48/0.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.48/0.73    inference(nnf_transformation,[],[f3])).
% 2.48/0.73  fof(f3,axiom,(
% 2.48/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.48/0.73  fof(f3232,plain,(
% 2.48/0.73    ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | (~spl9_1 | ~spl9_60)),
% 2.48/0.73    inference(forward_demodulation,[],[f3231,f2518])).
% 2.48/0.73  fof(f2518,plain,(
% 2.48/0.73    k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | ~spl9_60),
% 2.48/0.73    inference(avatar_component_clause,[],[f2516])).
% 2.48/0.73  fof(f2516,plain,(
% 2.48/0.73    spl9_60 <=> k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)),
% 2.48/0.73    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).
% 2.48/0.73  fof(f3231,plain,(
% 2.48/0.73    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_relat_1(sK4)) | (~spl9_1 | ~spl9_60)),
% 2.48/0.73    inference(subsumption_resolution,[],[f3230,f190])).
% 2.48/0.73  fof(f190,plain,(
% 2.48/0.73    v1_relat_1(sK4) | ~spl9_1),
% 2.48/0.73    inference(avatar_component_clause,[],[f189])).
% 2.48/0.73  fof(f189,plain,(
% 2.48/0.73    spl9_1 <=> v1_relat_1(sK4)),
% 2.48/0.73    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.48/0.73  fof(f3230,plain,(
% 2.48/0.73    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | ~spl9_60),
% 2.48/0.73    inference(subsumption_resolution,[],[f3229,f79])).
% 2.48/0.73  fof(f79,plain,(
% 2.48/0.73    v1_funct_1(sK4)),
% 2.48/0.73    inference(cnf_transformation,[],[f61])).
% 2.48/0.73  fof(f61,plain,(
% 2.48/0.73    k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2)) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 2.48/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f60])).
% 2.48/0.73  fof(f60,plain,(
% 2.48/0.73    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2)) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 2.48/0.73    introduced(choice_axiom,[])).
% 2.48/0.73  fof(f32,plain,(
% 2.48/0.73    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.48/0.73    inference(flattening,[],[f31])).
% 2.48/0.73  fof(f31,plain,(
% 2.48/0.73    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.48/0.73    inference(ennf_transformation,[],[f30])).
% 2.48/0.73  fof(f30,negated_conjecture,(
% 2.48/0.73    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 2.48/0.73    inference(negated_conjecture,[],[f29])).
% 2.48/0.73  fof(f29,conjecture,(
% 2.48/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 2.48/0.73  fof(f3229,plain,(
% 2.48/0.73    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~spl9_60),
% 2.48/0.73    inference(subsumption_resolution,[],[f3223,f772])).
% 2.48/0.73  fof(f772,plain,(
% 2.48/0.73    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4)),
% 2.48/0.73    inference(forward_demodulation,[],[f145,f630])).
% 2.48/0.73  fof(f630,plain,(
% 2.48/0.73    k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4)),
% 2.48/0.73    inference(resolution,[],[f129,f146])).
% 2.48/0.73  fof(f146,plain,(
% 2.48/0.73    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 2.48/0.73    inference(definition_unfolding,[],[f81,f144])).
% 2.48/0.73  fof(f144,plain,(
% 2.48/0.73    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.48/0.73    inference(definition_unfolding,[],[f90,f143])).
% 2.48/0.73  fof(f143,plain,(
% 2.48/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.48/0.73    inference(definition_unfolding,[],[f111,f127])).
% 2.48/0.73  fof(f127,plain,(
% 2.48/0.73    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f7])).
% 2.48/0.73  fof(f7,axiom,(
% 2.48/0.73    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.48/0.73  fof(f111,plain,(
% 2.48/0.73    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f6])).
% 2.48/0.73  fof(f6,axiom,(
% 2.48/0.73    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.48/0.73  fof(f90,plain,(
% 2.48/0.73    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f5])).
% 2.48/0.73  fof(f5,axiom,(
% 2.48/0.73    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.48/0.73  fof(f81,plain,(
% 2.48/0.73    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 2.48/0.73    inference(cnf_transformation,[],[f61])).
% 2.48/0.73  fof(f129,plain,(
% 2.48/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f50])).
% 2.48/0.73  fof(f50,plain,(
% 2.48/0.73    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/0.73    inference(ennf_transformation,[],[f26])).
% 2.48/0.73  fof(f26,axiom,(
% 2.48/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.48/0.73  fof(f145,plain,(
% 2.48/0.73    k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2))),
% 2.48/0.73    inference(definition_unfolding,[],[f83,f144,f144])).
% 2.48/0.73  fof(f83,plain,(
% 2.48/0.73    k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2))),
% 2.48/0.73    inference(cnf_transformation,[],[f61])).
% 2.48/0.73  fof(f3223,plain,(
% 2.48/0.73    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k1_relat_1(sK4)) | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~spl9_60),
% 2.48/0.73    inference(resolution,[],[f3105,f912])).
% 2.48/0.73  fof(f912,plain,(
% 2.48/0.73    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),k2_enumset1(X0,X0,X0,X0)) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1)) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.48/0.73    inference(extensionality_resolution,[],[f121,f152])).
% 2.48/0.73  fof(f152,plain,(
% 2.48/0.73    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.48/0.73    inference(definition_unfolding,[],[f117,f144,f144])).
% 2.48/0.73  fof(f117,plain,(
% 2.48/0.73    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f46])).
% 2.48/0.73  fof(f46,plain,(
% 2.48/0.73    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.48/0.73    inference(flattening,[],[f45])).
% 2.48/0.73  fof(f45,plain,(
% 2.48/0.73    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.48/0.73    inference(ennf_transformation,[],[f22])).
% 2.48/0.73  fof(f22,axiom,(
% 2.48/0.73    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 2.48/0.73  fof(f121,plain,(
% 2.48/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f73])).
% 2.48/0.73  fof(f3105,plain,(
% 2.48/0.73    ( ! [X2,X3] : (r1_tarski(k1_relat_1(sK4),k2_enumset1(X2,X2,X3,sK2))) ) | ~spl9_60),
% 2.48/0.73    inference(superposition,[],[f172,f2518])).
% 2.48/0.73  fof(f172,plain,(
% 2.48/0.73    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X1,X2))) )),
% 2.48/0.73    inference(equality_resolution,[],[f157])).
% 2.48/0.73  fof(f157,plain,(
% 2.48/0.73    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X2,X2,X2,X2) != X3) )),
% 2.48/0.73    inference(definition_unfolding,[],[f138,f127,f144])).
% 2.48/0.73  fof(f138,plain,(
% 2.48/0.73    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_tarski(X2) != X3) )),
% 2.48/0.73    inference(cnf_transformation,[],[f78])).
% 2.48/0.73  fof(f78,plain,(
% 2.48/0.73    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.48/0.73    inference(flattening,[],[f77])).
% 2.48/0.73  fof(f77,plain,(
% 2.48/0.73    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.48/0.73    inference(nnf_transformation,[],[f56])).
% 2.48/0.73  fof(f56,plain,(
% 2.48/0.73    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.48/0.73    inference(ennf_transformation,[],[f10])).
% 2.48/0.73  fof(f10,axiom,(
% 2.48/0.73    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 2.48/0.73  fof(f2997,plain,(
% 2.48/0.73    ~spl9_1 | ~spl9_5 | ~spl9_59),
% 2.48/0.73    inference(avatar_contradiction_clause,[],[f2996])).
% 2.48/0.73  fof(f2996,plain,(
% 2.48/0.73    $false | (~spl9_1 | ~spl9_5 | ~spl9_59)),
% 2.48/0.73    inference(subsumption_resolution,[],[f2956,f84])).
% 2.48/0.73  fof(f84,plain,(
% 2.48/0.73    v1_xboole_0(o_0_0_xboole_0)),
% 2.48/0.73    inference(cnf_transformation,[],[f1])).
% 2.48/0.73  fof(f1,axiom,(
% 2.48/0.73    v1_xboole_0(o_0_0_xboole_0)),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 2.48/0.73  fof(f2956,plain,(
% 2.48/0.73    ~v1_xboole_0(o_0_0_xboole_0) | (~spl9_1 | ~spl9_5 | ~spl9_59)),
% 2.48/0.73    inference(superposition,[],[f148,f2950])).
% 2.48/0.73  fof(f2950,plain,(
% 2.48/0.73    o_0_0_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | (~spl9_1 | ~spl9_5 | ~spl9_59)),
% 2.48/0.73    inference(forward_demodulation,[],[f2949,f458])).
% 2.48/0.73  fof(f458,plain,(
% 2.48/0.73    ( ! [X0] : (o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0)) )),
% 2.48/0.73    inference(forward_demodulation,[],[f457,f179])).
% 2.48/0.73  fof(f179,plain,(
% 2.48/0.73    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 2.48/0.73    inference(backward_demodulation,[],[f86,f176])).
% 2.48/0.73  fof(f176,plain,(
% 2.48/0.73    o_0_0_xboole_0 = k1_xboole_0),
% 2.48/0.73    inference(resolution,[],[f91,f84])).
% 2.48/0.73  fof(f91,plain,(
% 2.48/0.73    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.48/0.73    inference(cnf_transformation,[],[f33])).
% 2.48/0.73  fof(f33,plain,(
% 2.48/0.73    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.48/0.73    inference(ennf_transformation,[],[f2])).
% 2.48/0.73  fof(f2,axiom,(
% 2.48/0.73    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.48/0.73  fof(f86,plain,(
% 2.48/0.73    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.48/0.73    inference(cnf_transformation,[],[f18])).
% 2.48/0.73  fof(f18,axiom,(
% 2.48/0.73    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.48/0.73  fof(f457,plain,(
% 2.48/0.73    ( ! [X0] : (k2_relat_1(o_0_0_xboole_0) = k9_relat_1(o_0_0_xboole_0,X0)) )),
% 2.48/0.73    inference(forward_demodulation,[],[f378,f392])).
% 2.48/0.73  fof(f392,plain,(
% 2.48/0.73    ( ! [X1] : (o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X1)) )),
% 2.48/0.73    inference(subsumption_resolution,[],[f388,f202])).
% 2.48/0.73  fof(f202,plain,(
% 2.48/0.73    v1_relat_1(o_0_0_xboole_0)),
% 2.48/0.73    inference(resolution,[],[f128,f178])).
% 2.48/0.73  fof(f178,plain,(
% 2.48/0.73    ( ! [X0] : (m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))) )),
% 2.48/0.73    inference(backward_demodulation,[],[f89,f176])).
% 2.48/0.73  fof(f89,plain,(
% 2.48/0.73    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.48/0.73    inference(cnf_transformation,[],[f11])).
% 2.48/0.73  fof(f11,axiom,(
% 2.48/0.73    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.48/0.73  fof(f128,plain,(
% 2.48/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f49])).
% 2.48/0.73  fof(f49,plain,(
% 2.48/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/0.73    inference(ennf_transformation,[],[f23])).
% 2.48/0.73  fof(f23,axiom,(
% 2.48/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.48/0.73  fof(f388,plain,(
% 2.48/0.73    ( ! [X1] : (o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X1) | ~v1_relat_1(o_0_0_xboole_0)) )),
% 2.48/0.73    inference(resolution,[],[f118,f228])).
% 2.48/0.73  fof(f228,plain,(
% 2.48/0.73    ( ! [X0] : (v4_relat_1(o_0_0_xboole_0,X0)) )),
% 2.48/0.73    inference(subsumption_resolution,[],[f227,f202])).
% 2.48/0.73  fof(f227,plain,(
% 2.48/0.73    ( ! [X0] : (v4_relat_1(o_0_0_xboole_0,X0) | ~v1_relat_1(o_0_0_xboole_0)) )),
% 2.48/0.73    inference(subsumption_resolution,[],[f225,f181])).
% 2.48/0.73  fof(f181,plain,(
% 2.48/0.73    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 2.48/0.73    inference(backward_demodulation,[],[f88,f176])).
% 2.48/0.73  fof(f88,plain,(
% 2.48/0.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f4])).
% 2.48/0.73  fof(f4,axiom,(
% 2.48/0.73    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.48/0.73  fof(f225,plain,(
% 2.48/0.73    ( ! [X0] : (~r1_tarski(o_0_0_xboole_0,X0) | v4_relat_1(o_0_0_xboole_0,X0) | ~v1_relat_1(o_0_0_xboole_0)) )),
% 2.48/0.73    inference(superposition,[],[f115,f180])).
% 2.48/0.73  fof(f180,plain,(
% 2.48/0.73    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 2.48/0.73    inference(backward_demodulation,[],[f85,f176])).
% 2.48/0.73  fof(f85,plain,(
% 2.48/0.73    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.48/0.73    inference(cnf_transformation,[],[f18])).
% 2.48/0.73  fof(f115,plain,(
% 2.48/0.73    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f71])).
% 2.48/0.73  fof(f71,plain,(
% 2.48/0.73    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.48/0.73    inference(nnf_transformation,[],[f43])).
% 2.48/0.73  fof(f43,plain,(
% 2.48/0.73    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.48/0.73    inference(ennf_transformation,[],[f15])).
% 2.48/0.73  fof(f15,axiom,(
% 2.48/0.73    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.48/0.73  fof(f118,plain,(
% 2.48/0.73    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f48])).
% 2.48/0.73  fof(f48,plain,(
% 2.48/0.73    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.48/0.73    inference(flattening,[],[f47])).
% 2.48/0.73  fof(f47,plain,(
% 2.48/0.73    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.48/0.73    inference(ennf_transformation,[],[f17])).
% 2.48/0.73  fof(f17,axiom,(
% 2.48/0.73    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 2.48/0.73  fof(f378,plain,(
% 2.48/0.73    ( ! [X0] : (k2_relat_1(k7_relat_1(o_0_0_xboole_0,X0)) = k9_relat_1(o_0_0_xboole_0,X0)) )),
% 2.48/0.73    inference(resolution,[],[f113,f202])).
% 2.48/0.73  fof(f113,plain,(
% 2.48/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f42])).
% 2.48/0.73  fof(f42,plain,(
% 2.48/0.73    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.48/0.73    inference(ennf_transformation,[],[f16])).
% 2.48/0.73  fof(f16,axiom,(
% 2.48/0.73    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.48/0.73  fof(f2949,plain,(
% 2.48/0.73    ( ! [X8] : (k2_enumset1(sK2,sK2,sK2,sK2) = k9_relat_1(o_0_0_xboole_0,X8)) ) | (~spl9_1 | ~spl9_5 | ~spl9_59)),
% 2.48/0.73    inference(subsumption_resolution,[],[f2946,f353])).
% 2.48/0.73  fof(f353,plain,(
% 2.48/0.73    sP1(o_0_0_xboole_0) | ~spl9_5),
% 2.48/0.73    inference(subsumption_resolution,[],[f352,f202])).
% 2.48/0.73  fof(f352,plain,(
% 2.48/0.73    sP1(o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0) | ~spl9_5),
% 2.48/0.73    inference(resolution,[],[f295,f106])).
% 2.48/0.73  fof(f106,plain,(
% 2.48/0.73    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f59])).
% 2.48/0.73  fof(f59,plain,(
% 2.48/0.73    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.48/0.73    inference(definition_folding,[],[f39,f58,f57])).
% 2.48/0.73  fof(f57,plain,(
% 2.48/0.73    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0)))))),
% 2.48/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.48/0.73  fof(f58,plain,(
% 2.48/0.73    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> sP0(X0,X1,X2)) | ~sP1(X0))),
% 2.48/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.48/0.73  fof(f39,plain,(
% 2.48/0.73    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.48/0.73    inference(flattening,[],[f38])).
% 2.48/0.73  fof(f38,plain,(
% 2.48/0.73    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.48/0.73    inference(ennf_transformation,[],[f20])).
% 2.48/0.73  fof(f20,axiom,(
% 2.48/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 2.48/0.73  fof(f295,plain,(
% 2.48/0.73    v1_funct_1(o_0_0_xboole_0) | ~spl9_5),
% 2.48/0.73    inference(avatar_component_clause,[],[f294])).
% 2.48/0.73  fof(f294,plain,(
% 2.48/0.73    spl9_5 <=> v1_funct_1(o_0_0_xboole_0)),
% 2.48/0.73    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 2.48/0.73  fof(f2946,plain,(
% 2.48/0.73    ( ! [X8] : (k2_enumset1(sK2,sK2,sK2,sK2) = k9_relat_1(o_0_0_xboole_0,X8) | ~sP1(o_0_0_xboole_0)) ) | (~spl9_1 | ~spl9_59)),
% 2.48/0.73    inference(resolution,[],[f2913,f97])).
% 2.48/0.73  fof(f97,plain,(
% 2.48/0.73    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k9_relat_1(X0,X1) = X2 | ~sP1(X0)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f62])).
% 2.48/0.73  fof(f62,plain,(
% 2.48/0.73    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | k9_relat_1(X0,X1) != X2)) | ~sP1(X0))),
% 2.48/0.73    inference(nnf_transformation,[],[f58])).
% 2.48/0.73  fof(f2913,plain,(
% 2.48/0.73    ( ! [X8] : (sP0(o_0_0_xboole_0,X8,k2_enumset1(sK2,sK2,sK2,sK2))) ) | (~spl9_1 | ~spl9_59)),
% 2.48/0.73    inference(resolution,[],[f2794,f833])).
% 2.48/0.73  fof(f833,plain,(
% 2.48/0.73    ( ! [X0,X1] : (r2_hidden(sK5(o_0_0_xboole_0,X0,X1),X1) | sP0(o_0_0_xboole_0,X0,X1)) )),
% 2.48/0.73    inference(subsumption_resolution,[],[f829,f447])).
% 2.48/0.73  fof(f447,plain,(
% 2.48/0.73    ( ! [X19] : (~r2_hidden(X19,o_0_0_xboole_0)) )),
% 2.48/0.73    inference(subsumption_resolution,[],[f440,f148])).
% 2.48/0.73  fof(f440,plain,(
% 2.48/0.73    ( ! [X19] : (~r2_hidden(X19,o_0_0_xboole_0) | v1_xboole_0(k2_enumset1(X19,X19,X19,X19))) )),
% 2.48/0.73    inference(resolution,[],[f151,f368])).
% 2.48/0.73  fof(f368,plain,(
% 2.48/0.73    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0)) | v1_xboole_0(X1)) )),
% 2.48/0.73    inference(subsumption_resolution,[],[f357,f84])).
% 2.48/0.73  fof(f357,plain,(
% 2.48/0.73    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0)) | v1_xboole_0(X1) | ~v1_xboole_0(o_0_0_xboole_0)) )),
% 2.48/0.73    inference(superposition,[],[f112,f183])).
% 2.48/0.73  fof(f183,plain,(
% 2.48/0.73    ( ! [X0] : (o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0)) )),
% 2.48/0.73    inference(forward_demodulation,[],[f166,f176])).
% 2.48/0.73  fof(f166,plain,(
% 2.48/0.73    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.48/0.73    inference(equality_resolution,[],[f126])).
% 2.48/0.73  fof(f126,plain,(
% 2.48/0.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.48/0.73    inference(cnf_transformation,[],[f76])).
% 2.48/0.73  fof(f76,plain,(
% 2.48/0.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.48/0.73    inference(flattening,[],[f75])).
% 2.48/0.73  fof(f75,plain,(
% 2.48/0.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.48/0.73    inference(nnf_transformation,[],[f9])).
% 2.48/0.73  fof(f9,axiom,(
% 2.48/0.73    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.48/0.73  fof(f112,plain,(
% 2.48/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f41])).
% 2.48/0.73  fof(f41,plain,(
% 2.48/0.73    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.48/0.73    inference(ennf_transformation,[],[f25])).
% 2.48/0.73  fof(f25,axiom,(
% 2.48/0.73    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 2.48/0.73  fof(f151,plain,(
% 2.48/0.73    ( ! [X0,X1] : (m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.48/0.73    inference(definition_unfolding,[],[f116,f144])).
% 2.48/0.73  fof(f116,plain,(
% 2.48/0.73    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f44])).
% 2.48/0.73  fof(f44,plain,(
% 2.48/0.73    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.48/0.73    inference(ennf_transformation,[],[f12])).
% 2.48/0.73  fof(f12,axiom,(
% 2.48/0.73    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.48/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 2.48/0.73  fof(f829,plain,(
% 2.48/0.73    ( ! [X0,X1] : (r2_hidden(sK6(o_0_0_xboole_0,X0,X1),o_0_0_xboole_0) | r2_hidden(sK5(o_0_0_xboole_0,X0,X1),X1) | sP0(o_0_0_xboole_0,X0,X1)) )),
% 2.48/0.73    inference(superposition,[],[f102,f180])).
% 2.48/0.73  fof(f102,plain,(
% 2.48/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 2.48/0.73    inference(cnf_transformation,[],[f68])).
% 2.48/0.73  fof(f68,plain,(
% 2.48/0.73    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 2.48/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f64,f67,f66,f65])).
% 2.48/0.73  fof(f65,plain,(
% 2.48/0.73    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.48/0.73    introduced(choice_axiom,[])).
% 2.48/0.73  fof(f66,plain,(
% 2.48/0.73    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))))),
% 2.48/0.73    introduced(choice_axiom,[])).
% 2.48/0.73  fof(f67,plain,(
% 2.48/0.73    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))))),
% 2.48/0.73    introduced(choice_axiom,[])).
% 2.48/0.73  fof(f64,plain,(
% 2.48/0.73    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 2.48/0.73    inference(rectify,[],[f63])).
% 2.48/0.73  fof(f63,plain,(
% 2.48/0.73    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 2.48/0.73    inference(nnf_transformation,[],[f57])).
% 2.48/0.73  fof(f2794,plain,(
% 2.48/0.73    ( ! [X3] : (~r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2))) ) | (~spl9_1 | ~spl9_59)),
% 2.48/0.73    inference(subsumption_resolution,[],[f2793,f447])).
% 2.48/0.73  fof(f2793,plain,(
% 2.48/0.73    ( ! [X3] : (r2_hidden(k1_funct_1(o_0_0_xboole_0,X3),o_0_0_xboole_0) | ~r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2))) ) | (~spl9_1 | ~spl9_59)),
% 2.48/0.73    inference(forward_demodulation,[],[f2759,f179])).
% 2.71/0.73  fof(f2759,plain,(
% 2.71/0.73    ( ! [X3] : (r2_hidden(k1_funct_1(o_0_0_xboole_0,X3),k2_relat_1(o_0_0_xboole_0)) | ~r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2))) ) | (~spl9_1 | ~spl9_59)),
% 2.71/0.73    inference(backward_demodulation,[],[f888,f2720])).
% 2.71/0.73  fof(f2720,plain,(
% 2.71/0.73    o_0_0_xboole_0 = sK4 | (~spl9_1 | ~spl9_59)),
% 2.71/0.73    inference(resolution,[],[f2594,f236])).
% 2.71/0.73  fof(f236,plain,(
% 2.71/0.73    ( ! [X1] : (~r1_tarski(X1,o_0_0_xboole_0) | o_0_0_xboole_0 = X1) )),
% 2.71/0.73    inference(resolution,[],[f121,f181])).
% 2.71/0.73  fof(f2594,plain,(
% 2.71/0.73    r1_tarski(sK4,o_0_0_xboole_0) | (~spl9_1 | ~spl9_59)),
% 2.71/0.73    inference(forward_demodulation,[],[f2593,f184])).
% 2.71/0.73  fof(f184,plain,(
% 2.71/0.73    ( ! [X1] : (o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1)) )),
% 2.71/0.73    inference(forward_demodulation,[],[f167,f176])).
% 2.71/0.73  fof(f167,plain,(
% 2.71/0.73    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.71/0.73    inference(equality_resolution,[],[f125])).
% 2.71/0.73  fof(f125,plain,(
% 2.71/0.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.71/0.73    inference(cnf_transformation,[],[f76])).
% 2.71/0.73  fof(f2593,plain,(
% 2.71/0.73    r1_tarski(sK4,k2_zfmisc_1(o_0_0_xboole_0,k2_relat_1(sK4))) | (~spl9_1 | ~spl9_59)),
% 2.71/0.73    inference(subsumption_resolution,[],[f2592,f79])).
% 2.71/0.73  fof(f2592,plain,(
% 2.71/0.73    r1_tarski(sK4,k2_zfmisc_1(o_0_0_xboole_0,k2_relat_1(sK4))) | ~v1_funct_1(sK4) | (~spl9_1 | ~spl9_59)),
% 2.71/0.73    inference(subsumption_resolution,[],[f2548,f190])).
% 2.71/0.73  fof(f2548,plain,(
% 2.71/0.73    r1_tarski(sK4,k2_zfmisc_1(o_0_0_xboole_0,k2_relat_1(sK4))) | ~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~spl9_59),
% 2.71/0.73    inference(superposition,[],[f581,f2514])).
% 2.71/0.73  fof(f2514,plain,(
% 2.71/0.73    o_0_0_xboole_0 = k1_relat_1(sK4) | ~spl9_59),
% 2.71/0.73    inference(avatar_component_clause,[],[f2512])).
% 2.71/0.73  fof(f2512,plain,(
% 2.71/0.73    spl9_59 <=> o_0_0_xboole_0 = k1_relat_1(sK4)),
% 2.71/0.73    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 2.71/0.73  fof(f581,plain,(
% 2.71/0.73    ( ! [X7] : (r1_tarski(X7,k2_zfmisc_1(k1_relat_1(X7),k2_relat_1(X7))) | ~v1_relat_1(X7) | ~v1_funct_1(X7)) )),
% 2.71/0.73    inference(resolution,[],[f94,f122])).
% 2.71/0.73  fof(f122,plain,(
% 2.71/0.73    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.71/0.73    inference(cnf_transformation,[],[f74])).
% 2.71/0.73  fof(f74,plain,(
% 2.71/0.73    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.71/0.73    inference(nnf_transformation,[],[f13])).
% 2.71/0.73  fof(f13,axiom,(
% 2.71/0.73    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.71/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.71/0.73  fof(f94,plain,(
% 2.71/0.73    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.73    inference(cnf_transformation,[],[f35])).
% 2.71/0.73  fof(f35,plain,(
% 2.71/0.73    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.73    inference(flattening,[],[f34])).
% 2.71/0.73  fof(f34,plain,(
% 2.71/0.73    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/0.73    inference(ennf_transformation,[],[f27])).
% 2.71/0.73  fof(f27,axiom,(
% 2.71/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.71/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 2.71/0.73  fof(f888,plain,(
% 2.71/0.73    ( ! [X3] : (~r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2)) | r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))) )),
% 2.71/0.73    inference(subsumption_resolution,[],[f887,f79])).
% 2.71/0.73  fof(f887,plain,(
% 2.71/0.73    ( ! [X3] : (r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4)) | ~r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2)) | ~v1_funct_1(sK4)) )),
% 2.71/0.73    inference(subsumption_resolution,[],[f886,f147])).
% 2.71/0.73  fof(f147,plain,(
% 2.71/0.73    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 2.71/0.73    inference(definition_unfolding,[],[f80,f144])).
% 2.71/0.73  fof(f80,plain,(
% 2.71/0.73    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 2.71/0.73    inference(cnf_transformation,[],[f61])).
% 2.71/0.73  fof(f886,plain,(
% 2.71/0.73    ( ! [X3] : (r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4)) | ~r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2)) | ~v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) | ~v1_funct_1(sK4)) )),
% 2.71/0.73    inference(subsumption_resolution,[],[f885,f146])).
% 2.71/0.73  fof(f885,plain,(
% 2.71/0.73    ( ! [X3] : (r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4)) | ~r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) | ~v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) | ~v1_funct_1(sK4)) )),
% 2.71/0.73    inference(subsumption_resolution,[],[f881,f182])).
% 2.71/0.73  fof(f182,plain,(
% 2.71/0.73    o_0_0_xboole_0 != sK3),
% 2.71/0.73    inference(backward_demodulation,[],[f82,f176])).
% 2.71/0.73  fof(f82,plain,(
% 2.71/0.73    k1_xboole_0 != sK3),
% 2.71/0.73    inference(cnf_transformation,[],[f61])).
% 2.71/0.73  fof(f881,plain,(
% 2.71/0.73    ( ! [X3] : (r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4)) | o_0_0_xboole_0 = sK3 | ~r2_hidden(X3,k2_enumset1(sK2,sK2,sK2,sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) | ~v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) | ~v1_funct_1(sK4)) )),
% 2.71/0.73    inference(superposition,[],[f877,f630])).
% 2.71/0.73  fof(f877,plain,(
% 2.71/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.71/0.73    inference(forward_demodulation,[],[f133,f176])).
% 2.71/0.73  fof(f133,plain,(
% 2.71/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.71/0.73    inference(cnf_transformation,[],[f55])).
% 2.71/0.73  fof(f55,plain,(
% 2.71/0.73    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.71/0.73    inference(flattening,[],[f54])).
% 2.71/0.73  fof(f54,plain,(
% 2.71/0.73    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.71/0.73    inference(ennf_transformation,[],[f28])).
% 2.71/0.73  fof(f28,axiom,(
% 2.71/0.73    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 2.71/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 2.71/0.73  fof(f148,plain,(
% 2.71/0.73    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 2.71/0.73    inference(definition_unfolding,[],[f87,f144])).
% 2.71/0.73  fof(f87,plain,(
% 2.71/0.73    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.71/0.73    inference(cnf_transformation,[],[f8])).
% 2.71/0.73  fof(f8,axiom,(
% 2.71/0.73    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.71/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 2.71/0.73  fof(f2519,plain,(
% 2.71/0.73    spl9_59 | spl9_60 | ~spl9_1),
% 2.71/0.73    inference(avatar_split_clause,[],[f2510,f189,f2516,f2512])).
% 2.71/0.73  fof(f2510,plain,(
% 2.71/0.73    k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | o_0_0_xboole_0 = k1_relat_1(sK4) | ~spl9_1),
% 2.71/0.73    inference(subsumption_resolution,[],[f2504,f190])).
% 2.71/0.73  fof(f2504,plain,(
% 2.71/0.73    k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | o_0_0_xboole_0 = k1_relat_1(sK4) | ~v1_relat_1(sK4)),
% 2.71/0.73    inference(duplicate_literal_removal,[],[f2489])).
% 2.71/0.73  fof(f2489,plain,(
% 2.71/0.73    k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | o_0_0_xboole_0 = k1_relat_1(sK4) | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) | ~v1_relat_1(sK4)),
% 2.71/0.73    inference(resolution,[],[f974,f255])).
% 2.71/0.73  fof(f255,plain,(
% 2.71/0.73    v4_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))),
% 2.71/0.73    inference(resolution,[],[f130,f146])).
% 2.71/0.73  fof(f130,plain,(
% 2.71/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.71/0.73    inference(cnf_transformation,[],[f51])).
% 2.71/0.73  fof(f51,plain,(
% 2.71/0.73    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.73    inference(ennf_transformation,[],[f24])).
% 2.71/0.73  fof(f24,axiom,(
% 2.71/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.71/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.71/0.73  fof(f974,plain,(
% 2.71/0.73    ( ! [X39,X41,X42,X40] : (~v4_relat_1(X42,k2_enumset1(X39,X39,X40,X41)) | k1_relat_1(X42) = k2_enumset1(X39,X39,X39,X41) | k1_relat_1(X42) = k2_enumset1(X40,X40,X40,X41) | k1_relat_1(X42) = k2_enumset1(X39,X39,X39,X40) | k1_relat_1(X42) = k2_enumset1(X41,X41,X41,X41) | k1_relat_1(X42) = k2_enumset1(X40,X40,X40,X40) | k1_relat_1(X42) = k2_enumset1(X39,X39,X39,X39) | o_0_0_xboole_0 = k1_relat_1(X42) | k2_enumset1(X39,X39,X40,X41) = k1_relat_1(X42) | ~v1_relat_1(X42)) )),
% 2.71/0.73    inference(resolution,[],[f949,f114])).
% 2.71/0.73  fof(f114,plain,(
% 2.71/0.73    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.71/0.73    inference(cnf_transformation,[],[f71])).
% 2.71/0.73  fof(f949,plain,(
% 2.71/0.73    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | o_0_0_xboole_0 = X3) )),
% 2.71/0.73    inference(forward_demodulation,[],[f161,f176])).
% 2.71/0.73  fof(f161,plain,(
% 2.71/0.73    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.71/0.73    inference(definition_unfolding,[],[f134,f127,f143,f143,f143,f144,f144,f144,f127])).
% 2.71/0.73  fof(f134,plain,(
% 2.71/0.73    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.71/0.73    inference(cnf_transformation,[],[f78])).
% 2.71/0.73  fof(f2002,plain,(
% 2.71/0.73    ~spl9_7),
% 2.71/0.73    inference(avatar_contradiction_clause,[],[f2001])).
% 2.71/0.73  fof(f2001,plain,(
% 2.71/0.73    $false | ~spl9_7),
% 2.71/0.73    inference(subsumption_resolution,[],[f1996,f107])).
% 2.71/0.73  fof(f107,plain,(
% 2.71/0.73    ( ! [X0] : (v1_relat_1(sK8(X0))) )),
% 2.71/0.73    inference(cnf_transformation,[],[f70])).
% 2.71/0.73  fof(f70,plain,(
% 2.71/0.73    ! [X0] : (! [X2] : (k1_funct_1(sK8(X0),X2) = X0 | ~r2_hidden(X2,k1_tarski(k1_xboole_0))) & k1_tarski(k1_xboole_0) = k1_relat_1(sK8(X0)) & v1_funct_1(sK8(X0)) & v1_relat_1(sK8(X0)))),
% 2.71/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f69])).
% 2.71/0.73  fof(f69,plain,(
% 2.71/0.73    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = X0 | ~r2_hidden(X2,k1_tarski(k1_xboole_0))) & k1_relat_1(X1) = k1_tarski(k1_xboole_0) & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_funct_1(sK8(X0),X2) = X0 | ~r2_hidden(X2,k1_tarski(k1_xboole_0))) & k1_tarski(k1_xboole_0) = k1_relat_1(sK8(X0)) & v1_funct_1(sK8(X0)) & v1_relat_1(sK8(X0))))),
% 2.71/0.73    introduced(choice_axiom,[])).
% 2.71/0.73  fof(f40,plain,(
% 2.71/0.73    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = X0 | ~r2_hidden(X2,k1_tarski(k1_xboole_0))) & k1_relat_1(X1) = k1_tarski(k1_xboole_0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.71/0.73    inference(ennf_transformation,[],[f21])).
% 2.71/0.73  fof(f21,axiom,(
% 2.71/0.73    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,k1_tarski(k1_xboole_0)) => k1_funct_1(X1,X2) = X0) & k1_relat_1(X1) = k1_tarski(k1_xboole_0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.71/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e4_61_2__funct_1)).
% 2.71/0.73  fof(f1996,plain,(
% 2.71/0.73    ( ! [X1] : (~v1_relat_1(sK8(X1))) ) | ~spl9_7),
% 2.71/0.73    inference(resolution,[],[f350,f108])).
% 2.71/0.73  fof(f108,plain,(
% 2.71/0.73    ( ! [X0] : (v1_funct_1(sK8(X0))) )),
% 2.71/0.73    inference(cnf_transformation,[],[f70])).
% 2.71/0.73  fof(f350,plain,(
% 2.71/0.73    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl9_7),
% 2.71/0.73    inference(avatar_component_clause,[],[f349])).
% 2.71/0.73  fof(f349,plain,(
% 2.71/0.73    spl9_7 <=> ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.73    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 2.71/0.73  fof(f351,plain,(
% 2.71/0.73    spl9_7 | spl9_5),
% 2.71/0.73    inference(avatar_split_clause,[],[f338,f294,f349])).
% 2.71/0.73  fof(f338,plain,(
% 2.71/0.73    ( ! [X0] : (v1_funct_1(o_0_0_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.73    inference(resolution,[],[f95,f178])).
% 2.71/0.73  fof(f95,plain,(
% 2.71/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.73    inference(cnf_transformation,[],[f37])).
% 2.71/0.73  fof(f37,plain,(
% 2.71/0.73    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.73    inference(flattening,[],[f36])).
% 2.71/0.73  fof(f36,plain,(
% 2.71/0.73    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/0.73    inference(ennf_transformation,[],[f19])).
% 2.71/0.73  fof(f19,axiom,(
% 2.71/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 2.71/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).
% 2.71/0.73  fof(f208,plain,(
% 2.71/0.73    spl9_1),
% 2.71/0.73    inference(avatar_contradiction_clause,[],[f207])).
% 2.71/0.73  fof(f207,plain,(
% 2.71/0.73    $false | spl9_1),
% 2.71/0.73    inference(subsumption_resolution,[],[f204,f191])).
% 2.71/0.73  fof(f191,plain,(
% 2.71/0.73    ~v1_relat_1(sK4) | spl9_1),
% 2.71/0.73    inference(avatar_component_clause,[],[f189])).
% 2.71/0.73  fof(f204,plain,(
% 2.71/0.73    v1_relat_1(sK4)),
% 2.71/0.73    inference(resolution,[],[f128,f146])).
% 2.71/0.73  % SZS output end Proof for theBenchmark
% 2.71/0.73  % (9624)------------------------------
% 2.71/0.73  % (9624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.73  % (9624)Termination reason: Refutation
% 2.71/0.73  
% 2.71/0.73  % (9624)Memory used [KB]: 12792
% 2.71/0.73  % (9624)Time elapsed: 0.286 s
% 2.71/0.73  % (9624)------------------------------
% 2.71/0.73  % (9624)------------------------------
% 2.72/0.73  % (9617)Success in time 0.366 s
%------------------------------------------------------------------------------
