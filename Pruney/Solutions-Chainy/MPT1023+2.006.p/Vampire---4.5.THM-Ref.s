%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:07 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  122 (4273 expanded)
%              Number of leaves         :   15 (1344 expanded)
%              Depth                    :   31
%              Number of atoms          :  451 (29664 expanded)
%              Number of equality atoms :  164 (5937 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f914,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f635,f901,f153])).

fof(f153,plain,(
    ! [X2,X3] :
      ( r2_relset_1(k1_xboole_0,X2,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f106,f100])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f901,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK5,sK5) ),
    inference(forward_demodulation,[],[f856,f882])).

fof(f882,plain,(
    sK5 = sK6 ),
    inference(subsumption_resolution,[],[f870,f104])).

fof(f104,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f870,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | sK5 = sK6 ),
    inference(backward_demodulation,[],[f632,f848])).

fof(f848,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f847,f148])).

fof(f148,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f106,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f847,plain,
    ( ~ r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f846])).

fof(f846,plain,
    ( ~ r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f708,f684])).

fof(f684,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f683,f593])).

fof(f593,plain,(
    v1_funct_2(sK6,sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f63,f582])).

fof(f582,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f561,f149])).

fof(f149,plain,(
    r2_relset_1(sK3,sK4,sK5,sK5) ),
    inference(resolution,[],[f106,f61])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f37,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
              | ~ m1_subset_1(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK3,sK4,sK5,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
            | ~ m1_subset_1(X4,sK3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        & v1_funct_2(X3,sK3,sK4)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
      & ! [X4] :
          ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
          | ~ m1_subset_1(X4,sK3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f561,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK5)
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f66,f555])).

fof(f555,plain,
    ( sK5 = sK6
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f546,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f546,plain,
    ( sP0(sK3,sK4)
    | sK5 = sK6 ),
    inference(subsumption_resolution,[],[f544,f320])).

fof(f320,plain,
    ( ~ m1_subset_1(sK7(sK5,sK6),sK3)
    | sK5 = sK6
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f319,f245])).

fof(f245,plain,
    ( sK3 = k1_relat_1(sK5)
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f239,f60])).

fof(f60,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f239,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(resolution,[],[f156,f61])).

fof(f156,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f154,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f34,f33,f32])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f154,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f88,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f319,plain,
    ( sK3 != k1_relat_1(sK5)
    | sK5 = sK6
    | ~ m1_subset_1(sK7(sK5,sK6),sK3)
    | sP0(sK3,sK4) ),
    inference(superposition,[],[f270,f246])).

fof(f246,plain,
    ( sK3 = k1_relat_1(sK6)
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f240,f63])).

fof(f240,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(resolution,[],[f156,f64])).

fof(f64,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f270,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | sK5 = sK6
    | ~ m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(subsumption_resolution,[],[f269,f114])).

fof(f114,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f84,f61])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f269,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(subsumption_resolution,[],[f268,f59])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f268,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(X0,sK6),sK3) ) ),
    inference(subsumption_resolution,[],[f178,f115])).

fof(f115,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f84,f64])).

fof(f178,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(X0,sK6),sK3) ) ),
    inference(subsumption_resolution,[],[f173,f62])).

fof(f62,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f173,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(X0,sK6),sK3) ) ),
    inference(superposition,[],[f70,f65])).

fof(f65,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
            & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f544,plain,
    ( sK5 = sK6
    | sP0(sK3,sK4)
    | m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(resolution,[],[f542,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f542,plain,
    ( r2_hidden(sK7(sK5,sK6),sK3)
    | sK5 = sK6
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f541,f115])).

fof(f541,plain,
    ( r2_hidden(sK7(sK5,sK6),sK3)
    | sK5 = sK6
    | ~ v1_relat_1(sK6)
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f540,f62])).

fof(f540,plain,
    ( r2_hidden(sK7(sK5,sK6),sK3)
    | sK5 = sK6
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | sP0(sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f539])).

fof(f539,plain,
    ( sK3 != sK3
    | r2_hidden(sK7(sK5,sK6),sK3)
    | sK5 = sK6
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | sP0(sK3,sK4) ),
    inference(duplicate_literal_removal,[],[f537])).

fof(f537,plain,
    ( sK3 != sK3
    | r2_hidden(sK7(sK5,sK6),sK3)
    | sK5 = sK6
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | sP0(sK3,sK4)
    | sP0(sK3,sK4) ),
    inference(superposition,[],[f253,f246])).

fof(f253,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK3
      | r2_hidden(sK7(sK5,X1),sK3)
      | sK5 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sP0(sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f252,f114])).

fof(f252,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK3
      | r2_hidden(sK7(sK5,X1),sK3)
      | sK5 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK5)
      | sP0(sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f249,f59])).

fof(f249,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK3
      | r2_hidden(sK7(sK5,X1),sK3)
      | sK5 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5)
      | sP0(sK3,sK4) ) ),
    inference(superposition,[],[f69,f245])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f683,plain,
    ( ~ v1_funct_2(sK6,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f601,f103])).

fof(f103,plain,(
    ! [X2,X0] :
      ( ~ sP2(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f601,plain,(
    sP2(sK6,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f138,f582])).

fof(f138,plain,(
    sP2(sK6,sK4,sK3) ),
    inference(resolution,[],[f93,f64])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f708,plain,
    ( ~ r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,sK6)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f595,f682])).

fof(f682,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f681,f591])).

fof(f591,plain,(
    v1_funct_2(sK5,sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f60,f582])).

fof(f681,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5 ),
    inference(resolution,[],[f600,f103])).

fof(f600,plain,(
    sP2(sK5,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f137,f582])).

fof(f137,plain,(
    sP2(sK5,sK4,sK3) ),
    inference(resolution,[],[f93,f61])).

fof(f595,plain,(
    ~ r2_relset_1(sK3,k1_xboole_0,sK5,sK6) ),
    inference(backward_demodulation,[],[f66,f582])).

fof(f632,plain,
    ( sP0(sK3,k1_xboole_0)
    | sK5 = sK6 ),
    inference(backward_demodulation,[],[f546,f582])).

fof(f856,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK5,sK6) ),
    inference(backward_demodulation,[],[f595,f848])).

fof(f635,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f592,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f592,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f61,f582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (16461)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (16469)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (16472)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (16461)Refutation not found, incomplete strategy% (16461)------------------------------
% 0.21/0.52  % (16461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16468)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.53  % (16487)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.53  % (16461)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (16461)Memory used [KB]: 10874
% 1.32/0.53  % (16461)Time elapsed: 0.101 s
% 1.32/0.53  % (16461)------------------------------
% 1.32/0.53  % (16461)------------------------------
% 1.32/0.53  % (16462)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.53  % (16469)Refutation not found, incomplete strategy% (16469)------------------------------
% 1.32/0.53  % (16469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (16469)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (16469)Memory used [KB]: 10746
% 1.32/0.53  % (16469)Time elapsed: 0.104 s
% 1.32/0.53  % (16469)------------------------------
% 1.32/0.53  % (16469)------------------------------
% 1.32/0.53  % (16473)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.53  % (16483)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.53  % (16476)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.54  % (16464)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (16478)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.54  % (16465)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.54  % (16463)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (16488)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.55  % (16486)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.55  % (16481)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.55  % (16470)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.55  % (16459)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.49/0.55  % (16470)Refutation not found, incomplete strategy% (16470)------------------------------
% 1.49/0.55  % (16470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (16470)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (16470)Memory used [KB]: 10746
% 1.49/0.55  % (16470)Time elapsed: 0.148 s
% 1.49/0.55  % (16470)------------------------------
% 1.49/0.55  % (16470)------------------------------
% 1.49/0.56  % (16479)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.56  % (16477)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.56  % (16484)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.56  % (16474)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.49/0.57  % (16485)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.49/0.57  % (16460)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.57  % (16467)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.57  % (16466)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.58  % (16471)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.58  % (16480)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.58  % (16481)Refutation not found, incomplete strategy% (16481)------------------------------
% 1.49/0.58  % (16481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (16481)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (16481)Memory used [KB]: 11001
% 1.49/0.58  % (16481)Time elapsed: 0.118 s
% 1.49/0.58  % (16481)------------------------------
% 1.49/0.58  % (16481)------------------------------
% 1.49/0.58  % (16482)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.59  % (16475)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.59  % (16467)Refutation not found, incomplete strategy% (16467)------------------------------
% 1.49/0.59  % (16467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (16467)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (16467)Memory used [KB]: 10746
% 1.49/0.59  % (16467)Time elapsed: 0.166 s
% 1.49/0.59  % (16467)------------------------------
% 1.49/0.59  % (16467)------------------------------
% 1.49/0.60  % (16488)Refutation found. Thanks to Tanya!
% 1.49/0.60  % SZS status Theorem for theBenchmark
% 1.49/0.60  % SZS output start Proof for theBenchmark
% 1.49/0.60  fof(f914,plain,(
% 1.49/0.60    $false),
% 1.49/0.60    inference(unit_resulting_resolution,[],[f635,f901,f153])).
% 1.49/0.60  fof(f153,plain,(
% 1.49/0.60    ( ! [X2,X3] : (r2_relset_1(k1_xboole_0,X2,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))) )),
% 1.49/0.60    inference(superposition,[],[f106,f100])).
% 1.49/0.60  fof(f100,plain,(
% 1.49/0.60    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.49/0.60    inference(equality_resolution,[],[f82])).
% 1.49/0.60  fof(f82,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.49/0.60    inference(cnf_transformation,[],[f52])).
% 1.49/0.60  fof(f52,plain,(
% 1.49/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.49/0.60    inference(flattening,[],[f51])).
% 1.49/0.60  fof(f51,plain,(
% 1.49/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.49/0.60    inference(nnf_transformation,[],[f5])).
% 1.49/0.60  fof(f5,axiom,(
% 1.49/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.49/0.60  fof(f106,plain,(
% 1.49/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.49/0.60    inference(duplicate_literal_removal,[],[f105])).
% 1.49/0.60  fof(f105,plain,(
% 1.49/0.60    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.60    inference(equality_resolution,[],[f96])).
% 1.49/0.60  fof(f96,plain,(
% 1.49/0.60    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f58])).
% 1.49/0.60  fof(f58,plain,(
% 1.49/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(nnf_transformation,[],[f31])).
% 1.49/0.60  fof(f31,plain,(
% 1.49/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(flattening,[],[f30])).
% 1.49/0.60  fof(f30,plain,(
% 1.49/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.49/0.60    inference(ennf_transformation,[],[f13])).
% 1.49/0.60  fof(f13,axiom,(
% 1.49/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.49/0.60  fof(f901,plain,(
% 1.49/0.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK5,sK5)),
% 1.49/0.60    inference(forward_demodulation,[],[f856,f882])).
% 1.49/0.60  fof(f882,plain,(
% 1.49/0.60    sK5 = sK6),
% 1.49/0.60    inference(subsumption_resolution,[],[f870,f104])).
% 1.49/0.60  fof(f104,plain,(
% 1.49/0.60    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 1.49/0.60    inference(equality_resolution,[],[f91])).
% 1.49/0.60  fof(f91,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f57])).
% 1.49/0.60  fof(f57,plain,(
% 1.49/0.60    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.49/0.60    inference(nnf_transformation,[],[f32])).
% 1.49/0.60  fof(f32,plain,(
% 1.49/0.60    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.49/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.49/0.60  fof(f870,plain,(
% 1.49/0.60    sP0(k1_xboole_0,k1_xboole_0) | sK5 = sK6),
% 1.49/0.60    inference(backward_demodulation,[],[f632,f848])).
% 1.49/0.60  fof(f848,plain,(
% 1.49/0.60    k1_xboole_0 = sK3),
% 1.49/0.60    inference(subsumption_resolution,[],[f847,f148])).
% 1.49/0.60  fof(f148,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 1.49/0.60    inference(resolution,[],[f106,f68])).
% 1.49/0.60  fof(f68,plain,(
% 1.49/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f6])).
% 1.49/0.60  fof(f6,axiom,(
% 1.49/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.49/0.60  fof(f847,plain,(
% 1.49/0.60    ~r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK3),
% 1.49/0.60    inference(duplicate_literal_removal,[],[f846])).
% 1.49/0.60  fof(f846,plain,(
% 1.49/0.60    ~r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK3),
% 1.49/0.60    inference(superposition,[],[f708,f684])).
% 1.49/0.60  fof(f684,plain,(
% 1.49/0.60    k1_xboole_0 = sK6 | k1_xboole_0 = sK3),
% 1.49/0.60    inference(subsumption_resolution,[],[f683,f593])).
% 1.49/0.60  fof(f593,plain,(
% 1.49/0.60    v1_funct_2(sK6,sK3,k1_xboole_0)),
% 1.49/0.60    inference(backward_demodulation,[],[f63,f582])).
% 1.49/0.60  fof(f582,plain,(
% 1.49/0.60    k1_xboole_0 = sK4),
% 1.49/0.60    inference(subsumption_resolution,[],[f561,f149])).
% 1.49/0.60  fof(f149,plain,(
% 1.49/0.60    r2_relset_1(sK3,sK4,sK5,sK5)),
% 1.49/0.60    inference(resolution,[],[f106,f61])).
% 1.49/0.60  fof(f61,plain,(
% 1.49/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.49/0.60    inference(cnf_transformation,[],[f38])).
% 1.49/0.60  fof(f38,plain,(
% 1.49/0.60    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 1.49/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f37,f36])).
% 1.49/0.60  fof(f36,plain,(
% 1.49/0.60    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 1.49/0.60    introduced(choice_axiom,[])).
% 1.49/0.60  fof(f37,plain,(
% 1.49/0.60    ? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 1.49/0.60    introduced(choice_axiom,[])).
% 1.49/0.60  fof(f18,plain,(
% 1.49/0.60    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.49/0.60    inference(flattening,[],[f17])).
% 1.49/0.60  fof(f17,plain,(
% 1.49/0.60    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.49/0.60    inference(ennf_transformation,[],[f16])).
% 1.49/0.60  fof(f16,negated_conjecture,(
% 1.49/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.49/0.60    inference(negated_conjecture,[],[f15])).
% 1.49/0.60  fof(f15,conjecture,(
% 1.49/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).
% 1.49/0.60  fof(f561,plain,(
% 1.49/0.60    ~r2_relset_1(sK3,sK4,sK5,sK5) | k1_xboole_0 = sK4),
% 1.49/0.60    inference(superposition,[],[f66,f555])).
% 1.49/0.60  fof(f555,plain,(
% 1.49/0.60    sK5 = sK6 | k1_xboole_0 = sK4),
% 1.49/0.60    inference(resolution,[],[f546,f90])).
% 1.49/0.60  fof(f90,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 1.49/0.60    inference(cnf_transformation,[],[f57])).
% 1.49/0.60  fof(f546,plain,(
% 1.49/0.60    sP0(sK3,sK4) | sK5 = sK6),
% 1.49/0.60    inference(subsumption_resolution,[],[f544,f320])).
% 1.49/0.60  fof(f320,plain,(
% 1.49/0.60    ~m1_subset_1(sK7(sK5,sK6),sK3) | sK5 = sK6 | sP0(sK3,sK4)),
% 1.49/0.60    inference(subsumption_resolution,[],[f319,f245])).
% 1.49/0.60  fof(f245,plain,(
% 1.49/0.60    sK3 = k1_relat_1(sK5) | sP0(sK3,sK4)),
% 1.49/0.60    inference(subsumption_resolution,[],[f239,f60])).
% 1.49/0.60  fof(f60,plain,(
% 1.49/0.60    v1_funct_2(sK5,sK3,sK4)),
% 1.49/0.60    inference(cnf_transformation,[],[f38])).
% 1.49/0.60  fof(f239,plain,(
% 1.49/0.60    ~v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 1.49/0.60    inference(resolution,[],[f156,f61])).
% 1.49/0.60  fof(f156,plain,(
% 1.49/0.60    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f154,f92])).
% 1.49/0.60  fof(f92,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f35])).
% 1.49/0.60  fof(f35,plain,(
% 1.49/0.60    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(definition_folding,[],[f27,f34,f33,f32])).
% 1.49/0.60  fof(f33,plain,(
% 1.49/0.60    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.49/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.49/0.60  fof(f34,plain,(
% 1.49/0.60    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.49/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.49/0.60  fof(f27,plain,(
% 1.49/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(flattening,[],[f26])).
% 1.49/0.60  fof(f26,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(ennf_transformation,[],[f14])).
% 1.49/0.60  fof(f14,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.49/0.60  fof(f154,plain,(
% 1.49/0.60    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.49/0.60    inference(superposition,[],[f88,f85])).
% 1.49/0.60  fof(f85,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f25])).
% 1.49/0.60  fof(f25,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(ennf_transformation,[],[f12])).
% 1.49/0.60  fof(f12,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.49/0.60  fof(f88,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f56])).
% 1.49/0.60  fof(f56,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 1.49/0.60    inference(rectify,[],[f55])).
% 1.49/0.60  fof(f55,plain,(
% 1.49/0.60    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.49/0.60    inference(nnf_transformation,[],[f33])).
% 1.49/0.60  fof(f319,plain,(
% 1.49/0.60    sK3 != k1_relat_1(sK5) | sK5 = sK6 | ~m1_subset_1(sK7(sK5,sK6),sK3) | sP0(sK3,sK4)),
% 1.49/0.60    inference(superposition,[],[f270,f246])).
% 1.49/0.60  fof(f246,plain,(
% 1.49/0.60    sK3 = k1_relat_1(sK6) | sP0(sK3,sK4)),
% 1.49/0.60    inference(subsumption_resolution,[],[f240,f63])).
% 1.49/0.60  fof(f240,plain,(
% 1.49/0.60    ~v1_funct_2(sK6,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 1.49/0.60    inference(resolution,[],[f156,f64])).
% 1.49/0.60  fof(f64,plain,(
% 1.49/0.60    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.49/0.60    inference(cnf_transformation,[],[f38])).
% 1.49/0.60  fof(f270,plain,(
% 1.49/0.60    k1_relat_1(sK6) != k1_relat_1(sK5) | sK5 = sK6 | ~m1_subset_1(sK7(sK5,sK6),sK3)),
% 1.49/0.60    inference(subsumption_resolution,[],[f269,f114])).
% 1.49/0.60  fof(f114,plain,(
% 1.49/0.60    v1_relat_1(sK5)),
% 1.49/0.60    inference(resolution,[],[f84,f61])).
% 1.49/0.60  fof(f84,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f24])).
% 1.49/0.60  fof(f24,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.60    inference(ennf_transformation,[],[f10])).
% 1.49/0.60  fof(f10,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.49/0.60  fof(f269,plain,(
% 1.49/0.60    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~m1_subset_1(sK7(sK5,sK6),sK3)),
% 1.49/0.60    inference(subsumption_resolution,[],[f268,f59])).
% 1.49/0.60  fof(f59,plain,(
% 1.49/0.60    v1_funct_1(sK5)),
% 1.49/0.60    inference(cnf_transformation,[],[f38])).
% 1.49/0.60  fof(f268,plain,(
% 1.49/0.60    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~m1_subset_1(sK7(sK5,sK6),sK3)),
% 1.49/0.60    inference(equality_resolution,[],[f179])).
% 1.49/0.60  fof(f179,plain,(
% 1.49/0.60    ( ! [X0] : (k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(X0,sK6),sK3)) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f178,f115])).
% 1.49/0.60  fof(f115,plain,(
% 1.49/0.60    v1_relat_1(sK6)),
% 1.49/0.60    inference(resolution,[],[f84,f64])).
% 1.49/0.60  fof(f178,plain,(
% 1.49/0.60    ( ! [X0] : (k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(X0,sK6),sK3)) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f173,f62])).
% 1.49/0.60  fof(f62,plain,(
% 1.49/0.60    v1_funct_1(sK6)),
% 1.49/0.60    inference(cnf_transformation,[],[f38])).
% 1.49/0.60  fof(f173,plain,(
% 1.49/0.60    ( ! [X0] : (k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(X0,sK6),sK3)) )),
% 1.49/0.60    inference(superposition,[],[f70,f65])).
% 1.49/0.60  fof(f65,plain,(
% 1.49/0.60    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f38])).
% 1.49/0.60  fof(f70,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f40])).
% 1.49/0.60  fof(f40,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f39])).
% 1.49/0.60  fof(f39,plain,(
% 1.49/0.60    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 1.49/0.60    introduced(choice_axiom,[])).
% 1.49/0.60  fof(f20,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.60    inference(flattening,[],[f19])).
% 1.49/0.60  fof(f19,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.49/0.60    inference(ennf_transformation,[],[f9])).
% 1.49/0.60  fof(f9,axiom,(
% 1.49/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.49/0.60  fof(f544,plain,(
% 1.49/0.60    sK5 = sK6 | sP0(sK3,sK4) | m1_subset_1(sK7(sK5,sK6),sK3)),
% 1.49/0.60    inference(resolution,[],[f542,f74])).
% 1.49/0.60  fof(f74,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f22])).
% 1.49/0.60  fof(f22,plain,(
% 1.49/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.49/0.60    inference(ennf_transformation,[],[f7])).
% 1.49/0.60  fof(f7,axiom,(
% 1.49/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.49/0.60  fof(f542,plain,(
% 1.49/0.60    r2_hidden(sK7(sK5,sK6),sK3) | sK5 = sK6 | sP0(sK3,sK4)),
% 1.49/0.60    inference(subsumption_resolution,[],[f541,f115])).
% 1.49/0.60  fof(f541,plain,(
% 1.49/0.60    r2_hidden(sK7(sK5,sK6),sK3) | sK5 = sK6 | ~v1_relat_1(sK6) | sP0(sK3,sK4)),
% 1.49/0.60    inference(subsumption_resolution,[],[f540,f62])).
% 1.49/0.60  fof(f540,plain,(
% 1.49/0.60    r2_hidden(sK7(sK5,sK6),sK3) | sK5 = sK6 | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | sP0(sK3,sK4)),
% 1.49/0.60    inference(trivial_inequality_removal,[],[f539])).
% 1.49/0.60  fof(f539,plain,(
% 1.49/0.60    sK3 != sK3 | r2_hidden(sK7(sK5,sK6),sK3) | sK5 = sK6 | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | sP0(sK3,sK4)),
% 1.49/0.60    inference(duplicate_literal_removal,[],[f537])).
% 1.49/0.60  fof(f537,plain,(
% 1.49/0.60    sK3 != sK3 | r2_hidden(sK7(sK5,sK6),sK3) | sK5 = sK6 | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | sP0(sK3,sK4) | sP0(sK3,sK4)),
% 1.49/0.60    inference(superposition,[],[f253,f246])).
% 1.49/0.60  fof(f253,plain,(
% 1.49/0.60    ( ! [X1] : (k1_relat_1(X1) != sK3 | r2_hidden(sK7(sK5,X1),sK3) | sK5 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | sP0(sK3,sK4)) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f252,f114])).
% 1.49/0.60  fof(f252,plain,(
% 1.49/0.60    ( ! [X1] : (k1_relat_1(X1) != sK3 | r2_hidden(sK7(sK5,X1),sK3) | sK5 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK5) | sP0(sK3,sK4)) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f249,f59])).
% 1.49/0.60  fof(f249,plain,(
% 1.49/0.60    ( ! [X1] : (k1_relat_1(X1) != sK3 | r2_hidden(sK7(sK5,X1),sK3) | sK5 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sP0(sK3,sK4)) )),
% 1.49/0.60    inference(superposition,[],[f69,f245])).
% 1.49/0.60  fof(f69,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK7(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f40])).
% 1.49/0.60  fof(f66,plain,(
% 1.49/0.60    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 1.49/0.60    inference(cnf_transformation,[],[f38])).
% 1.49/0.60  fof(f63,plain,(
% 1.49/0.60    v1_funct_2(sK6,sK3,sK4)),
% 1.49/0.60    inference(cnf_transformation,[],[f38])).
% 1.49/0.60  fof(f683,plain,(
% 1.49/0.60    ~v1_funct_2(sK6,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK6),
% 1.49/0.60    inference(resolution,[],[f601,f103])).
% 1.49/0.60  fof(f103,plain,(
% 1.49/0.60    ( ! [X2,X0] : (~sP2(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 1.49/0.60    inference(equality_resolution,[],[f86])).
% 1.49/0.60  fof(f86,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f54])).
% 1.49/0.60  fof(f54,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 1.49/0.60    inference(rectify,[],[f53])).
% 1.49/0.60  fof(f53,plain,(
% 1.49/0.60    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.49/0.60    inference(nnf_transformation,[],[f34])).
% 1.49/0.60  fof(f601,plain,(
% 1.49/0.60    sP2(sK6,k1_xboole_0,sK3)),
% 1.49/0.60    inference(backward_demodulation,[],[f138,f582])).
% 1.49/0.60  fof(f138,plain,(
% 1.49/0.60    sP2(sK6,sK4,sK3)),
% 1.49/0.60    inference(resolution,[],[f93,f64])).
% 1.49/0.60  fof(f93,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f35])).
% 1.49/0.60  fof(f708,plain,(
% 1.49/0.60    ~r2_relset_1(sK3,k1_xboole_0,k1_xboole_0,sK6) | k1_xboole_0 = sK3),
% 1.49/0.60    inference(superposition,[],[f595,f682])).
% 1.49/0.60  fof(f682,plain,(
% 1.49/0.60    k1_xboole_0 = sK5 | k1_xboole_0 = sK3),
% 1.49/0.60    inference(subsumption_resolution,[],[f681,f591])).
% 1.49/0.60  fof(f591,plain,(
% 1.49/0.60    v1_funct_2(sK5,sK3,k1_xboole_0)),
% 1.49/0.60    inference(backward_demodulation,[],[f60,f582])).
% 1.49/0.60  fof(f681,plain,(
% 1.49/0.60    ~v1_funct_2(sK5,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5),
% 1.49/0.60    inference(resolution,[],[f600,f103])).
% 1.49/0.60  fof(f600,plain,(
% 1.49/0.60    sP2(sK5,k1_xboole_0,sK3)),
% 1.49/0.60    inference(backward_demodulation,[],[f137,f582])).
% 1.49/0.60  fof(f137,plain,(
% 1.49/0.60    sP2(sK5,sK4,sK3)),
% 1.49/0.60    inference(resolution,[],[f93,f61])).
% 1.49/0.60  fof(f595,plain,(
% 1.49/0.60    ~r2_relset_1(sK3,k1_xboole_0,sK5,sK6)),
% 1.49/0.60    inference(backward_demodulation,[],[f66,f582])).
% 1.49/0.60  fof(f632,plain,(
% 1.49/0.60    sP0(sK3,k1_xboole_0) | sK5 = sK6),
% 1.49/0.60    inference(backward_demodulation,[],[f546,f582])).
% 1.49/0.60  fof(f856,plain,(
% 1.49/0.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK5,sK6)),
% 1.49/0.60    inference(backward_demodulation,[],[f595,f848])).
% 1.49/0.60  fof(f635,plain,(
% 1.49/0.60    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 1.49/0.60    inference(forward_demodulation,[],[f592,f99])).
% 1.49/0.60  fof(f99,plain,(
% 1.49/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.49/0.60    inference(equality_resolution,[],[f83])).
% 1.49/0.60  fof(f83,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.49/0.60    inference(cnf_transformation,[],[f52])).
% 1.49/0.60  fof(f592,plain,(
% 1.49/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))),
% 1.49/0.60    inference(backward_demodulation,[],[f61,f582])).
% 1.49/0.60  % SZS output end Proof for theBenchmark
% 1.49/0.60  % (16488)------------------------------
% 1.49/0.60  % (16488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (16488)Termination reason: Refutation
% 1.49/0.60  
% 1.49/0.60  % (16488)Memory used [KB]: 2174
% 1.49/0.60  % (16488)Time elapsed: 0.139 s
% 1.49/0.60  % (16488)------------------------------
% 1.49/0.60  % (16488)------------------------------
% 1.49/0.60  % (16458)Success in time 0.245 s
%------------------------------------------------------------------------------
