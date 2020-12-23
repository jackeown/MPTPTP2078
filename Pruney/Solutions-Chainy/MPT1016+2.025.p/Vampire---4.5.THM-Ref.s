%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  163 (103065 expanded)
%              Number of leaves         :   18 (26790 expanded)
%              Depth                    :   68
%              Number of atoms          :  705 (818917 expanded)
%              Number of equality atoms :  259 (269570 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(subsumption_resolution,[],[f334,f289])).

fof(f289,plain,(
    sK8 != sK9 ),
    inference(subsumption_resolution,[],[f61,f285])).

fof(f285,plain,(
    v2_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f116,f284])).

fof(f284,plain,(
    sP3(sK7) ),
    inference(subsumption_resolution,[],[f283,f86])).

fof(f86,plain,(
    ! [X0] :
      ( sK12(X0) != sK13(X0)
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( sP3(X0)
        | ( sK12(X0) != sK13(X0)
          & k1_funct_1(X0,sK12(X0)) = k1_funct_1(X0,sK13(X0))
          & r2_hidden(sK13(X0),k1_relat_1(X0))
          & r2_hidden(sK12(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP3(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f48,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK12(X0) != sK13(X0)
        & k1_funct_1(X0,sK12(X0)) = k1_funct_1(X0,sK13(X0))
        & r2_hidden(sK13(X0),k1_relat_1(X0))
        & r2_hidden(sK12(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( sP3(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP3(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( sP3(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP3(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP3(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f283,plain,
    ( sK12(sK7) = sK13(sK7)
    | sP3(sK7) ),
    inference(subsumption_resolution,[],[f281,f85])).

fof(f85,plain,(
    ! [X0] :
      ( sP3(X0)
      | k1_funct_1(X0,sK12(X0)) = k1_funct_1(X0,sK13(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f281,plain,
    ( k1_funct_1(sK7,sK12(sK7)) != k1_funct_1(sK7,sK13(sK7))
    | sK12(sK7) = sK13(sK7)
    | sP3(sK7) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,
    ( k1_funct_1(sK7,sK12(sK7)) != k1_funct_1(sK7,sK13(sK7))
    | sK12(sK7) = sK13(sK7)
    | sP3(sK7)
    | sP3(sK7) ),
    inference(resolution,[],[f275,f262])).

fof(f262,plain,
    ( r2_hidden(sK13(sK7),k1_xboole_0)
    | sP3(sK7) ),
    inference(superposition,[],[f84,f257])).

fof(f257,plain,(
    k1_xboole_0 = k1_relat_1(sK7) ),
    inference(backward_demodulation,[],[f252,f256])).

fof(f256,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) ),
    inference(subsumption_resolution,[],[f254,f246])).

fof(f246,plain,(
    v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f55,f245])).

fof(f245,plain,(
    k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f244,f177])).

fof(f177,plain,
    ( sK8 != sK9
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f173,f61])).

fof(f173,plain,
    ( v2_funct_1(sK7)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f172,f116])).

fof(f172,plain,
    ( sP3(sK7)
    | k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f171,f86])).

fof(f171,plain,
    ( sK12(sK7) = sK13(sK7)
    | sP3(sK7)
    | k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f169,f85])).

fof(f169,plain,
    ( k1_funct_1(sK7,sK12(sK7)) != k1_funct_1(sK7,sK13(sK7))
    | sK12(sK7) = sK13(sK7)
    | sP3(sK7)
    | k1_xboole_0 = sK6 ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( k1_funct_1(sK7,sK12(sK7)) != k1_funct_1(sK7,sK13(sK7))
    | sK12(sK7) = sK13(sK7)
    | sP3(sK7)
    | k1_xboole_0 = sK6
    | sP3(sK7)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f141,f135])).

fof(f135,plain,
    ( r2_hidden(sK13(sK7),sK6)
    | sP3(sK7)
    | k1_xboole_0 = sK6 ),
    inference(superposition,[],[f84,f133])).

fof(f133,plain,
    ( sK6 = k1_relat_1(sK7)
    | k1_xboole_0 = sK6 ),
    inference(superposition,[],[f132,f127])).

fof(f127,plain,(
    k1_relset_1(sK6,sK6,sK7) = k1_relat_1(sK7) ),
    inference(resolution,[],[f89,f56])).

fof(f56,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK6))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ( sK8 != sK9
        & k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
        & r2_hidden(sK9,sK6)
        & r2_hidden(sK8,sK6) )
      | ~ v2_funct_1(sK7) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5)
          | ~ r2_hidden(X5,sK6)
          | ~ r2_hidden(X4,sK6) )
      | v2_funct_1(sK7) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK6)))
    & v1_funct_2(sK7,sK6,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK7,X2) = k1_funct_1(sK7,X3)
            & r2_hidden(X3,sK6)
            & r2_hidden(X2,sK6) )
        | ~ v2_funct_1(sK7) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5)
            | ~ r2_hidden(X5,sK6)
            | ~ r2_hidden(X4,sK6) )
        | v2_funct_1(sK7) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK6)))
      & v1_funct_2(sK7,sK6,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK7,X2) = k1_funct_1(sK7,X3)
        & r2_hidden(X3,sK6)
        & r2_hidden(X2,sK6) )
   => ( sK8 != sK9
      & k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
      & r2_hidden(sK9,sK6)
      & r2_hidden(sK8,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f132,plain,
    ( sK6 = k1_relset_1(sK6,sK6,sK7)
    | k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f131,f55])).

fof(f131,plain,
    ( ~ v1_funct_2(sK7,sK6,sK6)
    | k1_xboole_0 = sK6
    | sK6 = k1_relset_1(sK6,sK6,sK7) ),
    inference(resolution,[],[f90,f118])).

fof(f118,plain,(
    sP5(sK6,sK7,sK6) ),
    inference(resolution,[],[f94,f56])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP5(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP5(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP5(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP5(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP5(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f141,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK6)
      | k1_funct_1(sK7,X2) != k1_funct_1(sK7,sK12(sK7))
      | sK12(sK7) = X2
      | sP3(sK7)
      | k1_xboole_0 = sK6 ) ),
    inference(subsumption_resolution,[],[f139,f117])).

fof(f117,plain,
    ( ~ v2_funct_1(sK7)
    | sP3(sK7) ),
    inference(resolution,[],[f115,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ sP4(X0)
      | ~ v2_funct_1(X0)
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP3(X0) )
        & ( sP3(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP4(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP3(X0) )
      | ~ sP4(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f115,plain,(
    sP4(sK7) ),
    inference(subsumption_resolution,[],[f108,f114])).

fof(f114,plain,(
    v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f113,f88])).

fof(f88,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f113,plain,
    ( v1_relat_1(sK7)
    | ~ v1_relat_1(k2_zfmisc_1(sK6,sK6)) ),
    inference(resolution,[],[f62,f56])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f108,plain,
    ( ~ v1_relat_1(sK7)
    | sP4(sK7) ),
    inference(resolution,[],[f87,f54])).

fof(f54,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP4(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f18,f27,f26])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f139,plain,(
    ! [X2] :
      ( k1_funct_1(sK7,X2) != k1_funct_1(sK7,sK12(sK7))
      | ~ r2_hidden(X2,sK6)
      | sK12(sK7) = X2
      | v2_funct_1(sK7)
      | sP3(sK7)
      | k1_xboole_0 = sK6 ) ),
    inference(resolution,[],[f57,f136])).

fof(f136,plain,
    ( r2_hidden(sK12(sK7),sK6)
    | sP3(sK7)
    | k1_xboole_0 = sK6 ),
    inference(superposition,[],[f83,f133])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK12(X0),k1_relat_1(X0))
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f57,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK6)
      | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5)
      | ~ r2_hidden(X5,sK6)
      | X4 = X5
      | v2_funct_1(sK7) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f244,plain,
    ( sK8 = sK9
    | k1_xboole_0 = sK6 ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,
    ( sK8 = sK9
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK6 ),
    inference(superposition,[],[f239,f234])).

fof(f234,plain,
    ( sK8 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8))
    | k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f228,f173])).

fof(f228,plain,
    ( k1_xboole_0 = sK6
    | sK8 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8))
    | ~ v2_funct_1(sK7) ),
    inference(resolution,[],[f227,f58])).

fof(f58,plain,
    ( r2_hidden(sK8,sK6)
    | ~ v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f227,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | k1_xboole_0 = sK6
      | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | k1_xboole_0 = sK6
      | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0
      | k1_xboole_0 = sK6 ) ),
    inference(superposition,[],[f191,f133])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK7))
      | k1_xboole_0 = sK6
      | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0 ) ),
    inference(resolution,[],[f189,f98])).

fof(f98,plain,(
    ! [X0,X5,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | k1_funct_1(X0,k1_funct_1(X1,X5)) = X5 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X0,X4) = X5
      | k1_funct_1(X1,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( sK11(X0,X1) != k1_funct_1(X0,sK10(X0,X1))
            | ~ r2_hidden(sK10(X0,X1),k2_relat_1(X1)) )
          & sK10(X0,X1) = k1_funct_1(X1,sK11(X0,X1))
          & r2_hidden(sK11(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(sK10(X0,X1),sK11(X0,X1),X1,X0)
        | k1_relat_1(X0) != k2_relat_1(X1) )
      & ( ( ! [X4,X5] :
              ( ( ( k1_funct_1(X0,X4) = X5
                  & r2_hidden(X4,k2_relat_1(X1)) )
                | k1_funct_1(X1,X5) != X4
                | ~ r2_hidden(X5,k1_relat_1(X1)) )
              & sP0(X4,X5,X1,X0) )
          & k1_relat_1(X0) = k2_relat_1(X1) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X0,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X1)) )
            & k1_funct_1(X1,X3) = X2
            & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ sP0(X2,X3,X1,X0) )
     => ( ( ( sK11(X0,X1) != k1_funct_1(X0,sK10(X0,X1))
            | ~ r2_hidden(sK10(X0,X1),k2_relat_1(X1)) )
          & sK10(X0,X1) = k1_funct_1(X1,sK11(X0,X1))
          & r2_hidden(sK11(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(sK10(X0,X1),sK11(X0,X1),X1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2,X3] :
            ( ( ( k1_funct_1(X0,X2) != X3
                | ~ r2_hidden(X2,k2_relat_1(X1)) )
              & k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
            | ~ sP0(X2,X3,X1,X0) )
        | k1_relat_1(X0) != k2_relat_1(X1) )
      & ( ( ! [X4,X5] :
              ( ( ( k1_funct_1(X0,X4) = X5
                  & r2_hidden(X4,k2_relat_1(X1)) )
                | k1_funct_1(X1,X5) != X4
                | ~ r2_hidden(X5,k1_relat_1(X1)) )
              & sP0(X4,X5,X1,X0) )
          & k1_relat_1(X0) = k2_relat_1(X1) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ? [X2,X3] :
            ( ( ( k1_funct_1(X1,X2) != X3
                | ~ r2_hidden(X2,k2_relat_1(X0)) )
              & k1_funct_1(X0,X3) = X2
              & r2_hidden(X3,k1_relat_1(X0)) )
            | ~ sP0(X2,X3,X0,X1) )
        | k1_relat_1(X1) != k2_relat_1(X0) )
      & ( ( ! [X2,X3] :
              ( ( ( k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) )
                | k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
              & sP0(X2,X3,X0,X1) )
          & k1_relat_1(X1) = k2_relat_1(X0) )
        | ~ sP1(X1,X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ? [X2,X3] :
            ( ( ( k1_funct_1(X1,X2) != X3
                | ~ r2_hidden(X2,k2_relat_1(X0)) )
              & k1_funct_1(X0,X3) = X2
              & r2_hidden(X3,k1_relat_1(X0)) )
            | ~ sP0(X2,X3,X0,X1) )
        | k1_relat_1(X1) != k2_relat_1(X0) )
      & ( ( ! [X2,X3] :
              ( ( ( k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) )
                | k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
              & sP0(X2,X3,X0,X1) )
          & k1_relat_1(X1) = k2_relat_1(X0) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ( ! [X2,X3] :
            ( ( ( k1_funct_1(X1,X2) = X3
                & r2_hidden(X2,k2_relat_1(X0)) )
              | k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & sP0(X2,X3,X0,X1) )
        & k1_relat_1(X1) = k2_relat_1(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f189,plain,
    ( sP1(k2_funct_1(sK7),sK7)
    | k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f188,f114])).

fof(f188,plain,
    ( k1_xboole_0 = sK6
    | sP1(k2_funct_1(sK7),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f187,f54])).

fof(f187,plain,
    ( k1_xboole_0 = sK6
    | sP1(k2_funct_1(sK7),sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f186,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f186,plain,
    ( ~ v1_relat_1(k2_funct_1(sK7))
    | k1_xboole_0 = sK6
    | sP1(k2_funct_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f185,f114])).

fof(f185,plain,
    ( ~ v1_relat_1(k2_funct_1(sK7))
    | k1_xboole_0 = sK6
    | sP1(k2_funct_1(sK7),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f184,f54])).

fof(f184,plain,
    ( ~ v1_relat_1(k2_funct_1(sK7))
    | k1_xboole_0 = sK6
    | sP1(k2_funct_1(sK7),sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f182,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f182,plain,
    ( ~ v1_funct_1(k2_funct_1(sK7))
    | ~ v1_relat_1(k2_funct_1(sK7))
    | k1_xboole_0 = sK6
    | sP1(k2_funct_1(sK7),sK7) ),
    inference(resolution,[],[f180,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ sP2(X0,k2_funct_1(X0))
      | sP1(k2_funct_1(X0),X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | k2_funct_1(X0) != X1
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k2_funct_1(X0) = X1
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | k2_funct_1(X0) != X1 ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_funct_1(X0) = X1
      <=> sP1(X1,X0) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f180,plain,(
    ! [X0] :
      ( sP2(sK7,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK6 ) ),
    inference(subsumption_resolution,[],[f179,f114])).

fof(f179,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK6
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP2(sK7,X0)
      | ~ v1_relat_1(sK7) ) ),
    inference(subsumption_resolution,[],[f178,f54])).

fof(f178,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK6
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP2(sK7,X0)
      | ~ v1_funct_1(sK7)
      | ~ v1_relat_1(sK7) ) ),
    inference(resolution,[],[f173,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sP2(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f16,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f239,plain,
    ( sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8))
    | k1_xboole_0 = sK6 ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,
    ( sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK6 ),
    inference(superposition,[],[f235,f175])).

fof(f175,plain,
    ( k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f173,f60])).

fof(f60,plain,
    ( ~ v2_funct_1(sK7)
    | k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f235,plain,
    ( sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK9))
    | k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f229,f173])).

fof(f229,plain,
    ( k1_xboole_0 = sK6
    | sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK9))
    | ~ v2_funct_1(sK7) ),
    inference(resolution,[],[f227,f59])).

fof(f59,plain,
    ( r2_hidden(sK9,sK6)
    | ~ v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v1_funct_2(sK7,sK6,sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f254,plain,
    ( ~ v1_funct_2(sK7,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) ),
    inference(resolution,[],[f251,f104])).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ sP5(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f251,plain,(
    sP5(k1_xboole_0,sK7,k1_xboole_0) ),
    inference(backward_demodulation,[],[f118,f245])).

fof(f252,plain,(
    k1_relat_1(sK7) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) ),
    inference(backward_demodulation,[],[f127,f245])).

fof(f84,plain,(
    ! [X0] :
      ( r2_hidden(sK13(X0),k1_relat_1(X0))
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f275,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | k1_funct_1(sK7,X2) != k1_funct_1(sK7,sK12(sK7))
      | sK12(sK7) = X2
      | sP3(sK7) ) ),
    inference(subsumption_resolution,[],[f273,f117])).

fof(f273,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | k1_funct_1(sK7,X2) != k1_funct_1(sK7,sK12(sK7))
      | sK12(sK7) = X2
      | v2_funct_1(sK7)
      | sP3(sK7) ) ),
    inference(resolution,[],[f253,f263])).

fof(f263,plain,
    ( r2_hidden(sK12(sK7),k1_xboole_0)
    | sP3(sK7) ),
    inference(superposition,[],[f83,f257])).

fof(f253,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r2_hidden(X4,k1_xboole_0)
      | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5)
      | X4 = X5
      | v2_funct_1(sK7) ) ),
    inference(forward_demodulation,[],[f248,f245])).

fof(f248,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r2_hidden(X4,sK6)
      | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5)
      | X4 = X5
      | v2_funct_1(sK7) ) ),
    inference(backward_demodulation,[],[f57,f245])).

fof(f116,plain,
    ( ~ sP3(sK7)
    | v2_funct_1(sK7) ),
    inference(resolution,[],[f115,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ sP4(X0)
      | ~ sP3(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,
    ( ~ v2_funct_1(sK7)
    | sK8 != sK9 ),
    inference(cnf_transformation,[],[f36])).

fof(f334,plain,(
    sK8 = sK9 ),
    inference(backward_demodulation,[],[f333,f332])).

fof(f332,plain,(
    sK8 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8)) ),
    inference(resolution,[],[f312,f287])).

fof(f287,plain,(
    r2_hidden(sK8,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f249,f285])).

fof(f249,plain,
    ( r2_hidden(sK8,k1_xboole_0)
    | ~ v2_funct_1(sK7) ),
    inference(backward_demodulation,[],[f58,f245])).

fof(f312,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f308,f257])).

fof(f308,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK7))
      | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0 ) ),
    inference(resolution,[],[f306,f98])).

fof(f306,plain,(
    sP1(k2_funct_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f305,f114])).

fof(f305,plain,
    ( sP1(k2_funct_1(sK7),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f304,f54])).

fof(f304,plain,
    ( sP1(k2_funct_1(sK7),sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f303,f63])).

fof(f303,plain,
    ( ~ v1_relat_1(k2_funct_1(sK7))
    | sP1(k2_funct_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f302,f114])).

fof(f302,plain,
    ( ~ v1_relat_1(k2_funct_1(sK7))
    | sP1(k2_funct_1(sK7),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f301,f54])).

fof(f301,plain,
    ( ~ v1_relat_1(k2_funct_1(sK7))
    | sP1(k2_funct_1(sK7),sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f299,f64])).

fof(f299,plain,
    ( ~ v1_funct_1(k2_funct_1(sK7))
    | ~ v1_relat_1(k2_funct_1(sK7))
    | sP1(k2_funct_1(sK7),sK7) ),
    inference(resolution,[],[f292,f97])).

fof(f292,plain,(
    ! [X0] :
      ( sP2(sK7,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f291,f114])).

fof(f291,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP2(sK7,X0)
      | ~ v1_relat_1(sK7) ) ),
    inference(subsumption_resolution,[],[f290,f54])).

fof(f290,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP2(sK7,X0)
      | ~ v1_funct_1(sK7)
      | ~ v1_relat_1(sK7) ) ),
    inference(resolution,[],[f285,f79])).

fof(f333,plain,(
    sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8)) ),
    inference(forward_demodulation,[],[f331,f288])).

fof(f288,plain,(
    k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) ),
    inference(subsumption_resolution,[],[f60,f285])).

fof(f331,plain,(
    sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK9)) ),
    inference(resolution,[],[f312,f286])).

fof(f286,plain,(
    r2_hidden(sK9,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f250,f285])).

fof(f250,plain,
    ( r2_hidden(sK9,k1_xboole_0)
    | ~ v2_funct_1(sK7) ),
    inference(backward_demodulation,[],[f59,f245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:42:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (21314)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.47  % (21326)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (21310)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (21312)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (21320)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (21322)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (21320)Refutation not found, incomplete strategy% (21320)------------------------------
% 0.20/0.51  % (21320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21320)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21320)Memory used [KB]: 6140
% 0.20/0.51  % (21320)Time elapsed: 0.102 s
% 0.20/0.51  % (21320)------------------------------
% 0.20/0.51  % (21320)------------------------------
% 0.20/0.51  % (21307)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (21307)Refutation not found, incomplete strategy% (21307)------------------------------
% 0.20/0.51  % (21307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21307)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21307)Memory used [KB]: 10618
% 0.20/0.51  % (21307)Time elapsed: 0.106 s
% 0.20/0.51  % (21307)------------------------------
% 0.20/0.51  % (21307)------------------------------
% 0.20/0.51  % (21309)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (21317)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (21319)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (21315)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (21325)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (21318)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (21330)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (21329)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (21327)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (21310)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f335,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f334,f289])).
% 0.20/0.53  fof(f289,plain,(
% 0.20/0.53    sK8 != sK9),
% 0.20/0.53    inference(subsumption_resolution,[],[f61,f285])).
% 0.20/0.53  fof(f285,plain,(
% 0.20/0.53    v2_funct_1(sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f116,f284])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    sP3(sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f283,f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X0] : (sK12(X0) != sK13(X0) | sP3(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X0] : ((sP3(X0) | (sK12(X0) != sK13(X0) & k1_funct_1(X0,sK12(X0)) = k1_funct_1(X0,sK13(X0)) & r2_hidden(sK13(X0),k1_relat_1(X0)) & r2_hidden(sK12(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP3(X0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f48,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK12(X0) != sK13(X0) & k1_funct_1(X0,sK12(X0)) = k1_funct_1(X0,sK13(X0)) & r2_hidden(sK13(X0),k1_relat_1(X0)) & r2_hidden(sK12(X0),k1_relat_1(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ! [X0] : ((sP3(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP3(X0)))),
% 0.20/0.53    inference(rectify,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0] : ((sP3(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP3(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (sP3(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.53  fof(f283,plain,(
% 0.20/0.53    sK12(sK7) = sK13(sK7) | sP3(sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f281,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0] : (sP3(X0) | k1_funct_1(X0,sK12(X0)) = k1_funct_1(X0,sK13(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f50])).
% 0.20/0.53  fof(f281,plain,(
% 0.20/0.53    k1_funct_1(sK7,sK12(sK7)) != k1_funct_1(sK7,sK13(sK7)) | sK12(sK7) = sK13(sK7) | sP3(sK7)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f280])).
% 0.20/0.53  fof(f280,plain,(
% 0.20/0.53    k1_funct_1(sK7,sK12(sK7)) != k1_funct_1(sK7,sK13(sK7)) | sK12(sK7) = sK13(sK7) | sP3(sK7) | sP3(sK7)),
% 0.20/0.53    inference(resolution,[],[f275,f262])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    r2_hidden(sK13(sK7),k1_xboole_0) | sP3(sK7)),
% 0.20/0.53    inference(superposition,[],[f84,f257])).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(sK7)),
% 0.20/0.53    inference(backward_demodulation,[],[f252,f256])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f254,f246])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    v1_funct_2(sK7,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f55,f245])).
% 0.20/0.53  fof(f245,plain,(
% 0.20/0.53    k1_xboole_0 = sK6),
% 0.20/0.53    inference(subsumption_resolution,[],[f244,f177])).
% 0.20/0.53  fof(f177,plain,(
% 0.20/0.53    sK8 != sK9 | k1_xboole_0 = sK6),
% 0.20/0.53    inference(resolution,[],[f173,f61])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    v2_funct_1(sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(resolution,[],[f172,f116])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    sP3(sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(subsumption_resolution,[],[f171,f86])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    sK12(sK7) = sK13(sK7) | sP3(sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(subsumption_resolution,[],[f169,f85])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    k1_funct_1(sK7,sK12(sK7)) != k1_funct_1(sK7,sK13(sK7)) | sK12(sK7) = sK13(sK7) | sP3(sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f168])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    k1_funct_1(sK7,sK12(sK7)) != k1_funct_1(sK7,sK13(sK7)) | sK12(sK7) = sK13(sK7) | sP3(sK7) | k1_xboole_0 = sK6 | sP3(sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(resolution,[],[f141,f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    r2_hidden(sK13(sK7),sK6) | sP3(sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(superposition,[],[f84,f133])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    sK6 = k1_relat_1(sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(superposition,[],[f132,f127])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    k1_relset_1(sK6,sK6,sK7) = k1_relat_1(sK7)),
% 0.20/0.53    inference(resolution,[],[f89,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK6)))),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ((sK8 != sK9 & k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) & r2_hidden(sK9,sK6) & r2_hidden(sK8,sK6)) | ~v2_funct_1(sK7)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5) | ~r2_hidden(X5,sK6) | ~r2_hidden(X4,sK6)) | v2_funct_1(sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK6))) & v1_funct_2(sK7,sK6,sK6) & v1_funct_1(sK7)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f35,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK7,X2) = k1_funct_1(sK7,X3) & r2_hidden(X3,sK6) & r2_hidden(X2,sK6)) | ~v2_funct_1(sK7)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5) | ~r2_hidden(X5,sK6) | ~r2_hidden(X4,sK6)) | v2_funct_1(sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK6))) & v1_funct_2(sK7,sK6,sK6) & v1_funct_1(sK7))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK7,X2) = k1_funct_1(sK7,X3) & r2_hidden(X3,sK6) & r2_hidden(X2,sK6)) => (sK8 != sK9 & k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) & r2_hidden(sK9,sK6) & r2_hidden(sK8,sK6))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.53    inference(rectify,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.53    inference(flattening,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    sK6 = k1_relset_1(sK6,sK6,sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(subsumption_resolution,[],[f131,f55])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    ~v1_funct_2(sK7,sK6,sK6) | k1_xboole_0 = sK6 | sK6 = k1_relset_1(sK6,sK6,sK7)),
% 0.20/0.53    inference(resolution,[],[f90,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    sP5(sK6,sK7,sK6)),
% 0.20/0.53    inference(resolution,[],[f94,f56])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP5(X0,X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP5(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP5(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(definition_folding,[],[f21,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP5(X0,X2,X1))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP5(X0,X1,X2))),
% 0.20/0.53    inference(rectify,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP5(X0,X2,X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f29])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    ( ! [X2] : (~r2_hidden(X2,sK6) | k1_funct_1(sK7,X2) != k1_funct_1(sK7,sK12(sK7)) | sK12(sK7) = X2 | sP3(sK7) | k1_xboole_0 = sK6) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f139,f117])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    ~v2_funct_1(sK7) | sP3(sK7)),
% 0.20/0.53    inference(resolution,[],[f115,f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X0] : (~sP4(X0) | ~v2_funct_1(X0) | sP3(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X0] : (((v2_funct_1(X0) | ~sP3(X0)) & (sP3(X0) | ~v2_funct_1(X0))) | ~sP4(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : ((v2_funct_1(X0) <=> sP3(X0)) | ~sP4(X0))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    sP4(sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f108,f114])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    v1_relat_1(sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f113,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    v1_relat_1(sK7) | ~v1_relat_1(k2_zfmisc_1(sK6,sK6))),
% 0.20/0.53    inference(resolution,[],[f62,f56])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ~v1_relat_1(sK7) | sP4(sK7)),
% 0.20/0.53    inference(resolution,[],[f87,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    v1_funct_1(sK7)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_funct_1(X0) | sP4(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0] : (sP4(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(definition_folding,[],[f18,f27,f26])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ( ! [X2] : (k1_funct_1(sK7,X2) != k1_funct_1(sK7,sK12(sK7)) | ~r2_hidden(X2,sK6) | sK12(sK7) = X2 | v2_funct_1(sK7) | sP3(sK7) | k1_xboole_0 = sK6) )),
% 0.20/0.53    inference(resolution,[],[f57,f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    r2_hidden(sK12(sK7),sK6) | sP3(sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(superposition,[],[f83,f133])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK12(X0),k1_relat_1(X0)) | sP3(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f50])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X4,X5] : (~r2_hidden(X4,sK6) | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5) | ~r2_hidden(X5,sK6) | X4 = X5 | v2_funct_1(sK7)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    sK8 = sK9 | k1_xboole_0 = sK6),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f240])).
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    sK8 = sK9 | k1_xboole_0 = sK6 | k1_xboole_0 = sK6),
% 0.20/0.53    inference(superposition,[],[f239,f234])).
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    sK8 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8)) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(subsumption_resolution,[],[f228,f173])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    k1_xboole_0 = sK6 | sK8 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8)) | ~v2_funct_1(sK7)),
% 0.20/0.53    inference(resolution,[],[f227,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    r2_hidden(sK8,sK6) | ~v2_funct_1(sK7)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK6) | k1_xboole_0 = sK6 | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f226])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK6) | k1_xboole_0 = sK6 | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0 | k1_xboole_0 = sK6) )),
% 0.20/0.53    inference(superposition,[],[f191,f133])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK7)) | k1_xboole_0 = sK6 | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0) )),
% 0.20/0.53    inference(resolution,[],[f189,f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X0,X5,X1] : (~sP1(X0,X1) | ~r2_hidden(X5,k1_relat_1(X1)) | k1_funct_1(X0,k1_funct_1(X1,X5)) = X5) )),
% 0.20/0.53    inference(equality_resolution,[],[f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X4,X0,X5,X1] : (k1_funct_1(X0,X4) = X5 | k1_funct_1(X1,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X1)) | ~sP1(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP1(X0,X1) | (((sK11(X0,X1) != k1_funct_1(X0,sK10(X0,X1)) | ~r2_hidden(sK10(X0,X1),k2_relat_1(X1))) & sK10(X0,X1) = k1_funct_1(X1,sK11(X0,X1)) & r2_hidden(sK11(X0,X1),k1_relat_1(X1))) | ~sP0(sK10(X0,X1),sK11(X0,X1),X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X0,X4) = X5 & r2_hidden(X4,k2_relat_1(X1))) | k1_funct_1(X1,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X1))) & sP0(X4,X5,X1,X0)) & k1_relat_1(X0) = k2_relat_1(X1)) | ~sP1(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f40,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X0,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X1))) & k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X2,X3,X1,X0)) => (((sK11(X0,X1) != k1_funct_1(X0,sK10(X0,X1)) | ~r2_hidden(sK10(X0,X1),k2_relat_1(X1))) & sK10(X0,X1) = k1_funct_1(X1,sK11(X0,X1)) & r2_hidden(sK11(X0,X1),k1_relat_1(X1))) | ~sP0(sK10(X0,X1),sK11(X0,X1),X1,X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP1(X0,X1) | ? [X2,X3] : (((k1_funct_1(X0,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X1))) & k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X2,X3,X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X0,X4) = X5 & r2_hidden(X4,k2_relat_1(X1))) | k1_funct_1(X1,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X1))) & sP0(X4,X5,X1,X0)) & k1_relat_1(X0) = k2_relat_1(X1)) | ~sP1(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X1,X0] : ((sP1(X1,X0) | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | ~sP1(X1,X0)))),
% 0.20/0.53    inference(flattening,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X1,X0] : ((sP1(X1,X0) | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | ~sP1(X1,X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X1,X0] : (sP1(X1,X0) <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    sP1(k2_funct_1(sK7),sK7) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(subsumption_resolution,[],[f188,f114])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    k1_xboole_0 = sK6 | sP1(k2_funct_1(sK7),sK7) | ~v1_relat_1(sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f187,f54])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    k1_xboole_0 = sK6 | sP1(k2_funct_1(sK7),sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)),
% 0.20/0.53    inference(resolution,[],[f186,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    ~v1_relat_1(k2_funct_1(sK7)) | k1_xboole_0 = sK6 | sP1(k2_funct_1(sK7),sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f185,f114])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    ~v1_relat_1(k2_funct_1(sK7)) | k1_xboole_0 = sK6 | sP1(k2_funct_1(sK7),sK7) | ~v1_relat_1(sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f184,f54])).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    ~v1_relat_1(k2_funct_1(sK7)) | k1_xboole_0 = sK6 | sP1(k2_funct_1(sK7),sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)),
% 0.20/0.53    inference(resolution,[],[f182,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    ~v1_funct_1(k2_funct_1(sK7)) | ~v1_relat_1(k2_funct_1(sK7)) | k1_xboole_0 = sK6 | sP1(k2_funct_1(sK7),sK7)),
% 0.20/0.53    inference(resolution,[],[f180,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X0] : (~sP2(X0,k2_funct_1(X0)) | sP1(k2_funct_1(X0),X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP1(X1,X0) | k2_funct_1(X0) != X1 | ~sP2(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1] : (((k2_funct_1(X0) = X1 | ~sP1(X1,X0)) & (sP1(X1,X0) | k2_funct_1(X0) != X1)) | ~sP2(X0,X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_funct_1(X0) = X1 <=> sP1(X1,X0)) | ~sP2(X0,X1))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    ( ! [X0] : (sP2(sK7,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK6) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f179,f114])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = sK6 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP2(sK7,X0) | ~v1_relat_1(sK7)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f178,f54])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = sK6 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP2(sK7,X0) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) )),
% 0.20/0.53    inference(resolution,[],[f173,f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | sP2(X0,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (sP2(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(definition_folding,[],[f16,f24,f23,f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).
% 0.20/0.53  fof(f239,plain,(
% 0.20/0.53    sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8)) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f237])).
% 0.20/0.53  fof(f237,plain,(
% 0.20/0.53    sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8)) | k1_xboole_0 = sK6 | k1_xboole_0 = sK6),
% 0.20/0.53    inference(superposition,[],[f235,f175])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(resolution,[],[f173,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ~v2_funct_1(sK7) | k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK9)) | k1_xboole_0 = sK6),
% 0.20/0.53    inference(subsumption_resolution,[],[f229,f173])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    k1_xboole_0 = sK6 | sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK9)) | ~v2_funct_1(sK7)),
% 0.20/0.53    inference(resolution,[],[f227,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    r2_hidden(sK9,sK6) | ~v2_funct_1(sK7)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    v1_funct_2(sK7,sK6,sK6)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f254,plain,(
% 0.20/0.53    ~v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK7)),
% 0.20/0.53    inference(resolution,[],[f251,f104])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~sP5(k1_xboole_0,X1,X2) | ~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP5(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f52])).
% 0.20/0.53  fof(f251,plain,(
% 0.20/0.53    sP5(k1_xboole_0,sK7,k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f118,f245])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    k1_relat_1(sK7) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK7)),
% 0.20/0.53    inference(backward_demodulation,[],[f127,f245])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK13(X0),k1_relat_1(X0)) | sP3(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f50])).
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | k1_funct_1(sK7,X2) != k1_funct_1(sK7,sK12(sK7)) | sK12(sK7) = X2 | sP3(sK7)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f273,f117])).
% 0.20/0.53  fof(f273,plain,(
% 0.20/0.53    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | k1_funct_1(sK7,X2) != k1_funct_1(sK7,sK12(sK7)) | sK12(sK7) = X2 | v2_funct_1(sK7) | sP3(sK7)) )),
% 0.20/0.53    inference(resolution,[],[f253,f263])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    r2_hidden(sK12(sK7),k1_xboole_0) | sP3(sK7)),
% 0.20/0.53    inference(superposition,[],[f83,f257])).
% 0.20/0.53  fof(f253,plain,(
% 0.20/0.53    ( ! [X4,X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0) | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5) | X4 = X5 | v2_funct_1(sK7)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f248,f245])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    ( ! [X4,X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X4,sK6) | k1_funct_1(sK7,X4) != k1_funct_1(sK7,X5) | X4 = X5 | v2_funct_1(sK7)) )),
% 0.20/0.53    inference(backward_demodulation,[],[f57,f245])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ~sP3(sK7) | v2_funct_1(sK7)),
% 0.20/0.53    inference(resolution,[],[f115,f81])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X0] : (~sP4(X0) | ~sP3(X0) | v2_funct_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ~v2_funct_1(sK7) | sK8 != sK9),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f334,plain,(
% 0.20/0.53    sK8 = sK9),
% 0.20/0.53    inference(backward_demodulation,[],[f333,f332])).
% 0.20/0.53  fof(f332,plain,(
% 0.20/0.53    sK8 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8))),
% 0.20/0.53    inference(resolution,[],[f312,f287])).
% 0.20/0.53  fof(f287,plain,(
% 0.20/0.53    r2_hidden(sK8,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f249,f285])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    r2_hidden(sK8,k1_xboole_0) | ~v2_funct_1(sK7)),
% 0.20/0.53    inference(backward_demodulation,[],[f58,f245])).
% 0.20/0.53  fof(f312,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0) )),
% 0.20/0.53    inference(forward_demodulation,[],[f308,f257])).
% 0.20/0.53  fof(f308,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK7)) | k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,X0)) = X0) )),
% 0.20/0.53    inference(resolution,[],[f306,f98])).
% 0.20/0.53  fof(f306,plain,(
% 0.20/0.53    sP1(k2_funct_1(sK7),sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f305,f114])).
% 0.20/0.53  fof(f305,plain,(
% 0.20/0.53    sP1(k2_funct_1(sK7),sK7) | ~v1_relat_1(sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f304,f54])).
% 0.20/0.53  fof(f304,plain,(
% 0.20/0.53    sP1(k2_funct_1(sK7),sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)),
% 0.20/0.53    inference(resolution,[],[f303,f63])).
% 0.20/0.53  fof(f303,plain,(
% 0.20/0.53    ~v1_relat_1(k2_funct_1(sK7)) | sP1(k2_funct_1(sK7),sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f302,f114])).
% 0.20/0.53  fof(f302,plain,(
% 0.20/0.53    ~v1_relat_1(k2_funct_1(sK7)) | sP1(k2_funct_1(sK7),sK7) | ~v1_relat_1(sK7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f301,f54])).
% 0.20/0.53  fof(f301,plain,(
% 0.20/0.53    ~v1_relat_1(k2_funct_1(sK7)) | sP1(k2_funct_1(sK7),sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)),
% 0.20/0.53    inference(resolution,[],[f299,f64])).
% 0.20/0.53  fof(f299,plain,(
% 0.20/0.53    ~v1_funct_1(k2_funct_1(sK7)) | ~v1_relat_1(k2_funct_1(sK7)) | sP1(k2_funct_1(sK7),sK7)),
% 0.20/0.53    inference(resolution,[],[f292,f97])).
% 0.20/0.53  fof(f292,plain,(
% 0.20/0.53    ( ! [X0] : (sP2(sK7,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f291,f114])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP2(sK7,X0) | ~v1_relat_1(sK7)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f290,f54])).
% 0.20/0.53  fof(f290,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP2(sK7,X0) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) )),
% 0.20/0.53    inference(resolution,[],[f285,f79])).
% 0.20/0.53  fof(f333,plain,(
% 0.20/0.53    sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK8))),
% 0.20/0.53    inference(forward_demodulation,[],[f331,f288])).
% 0.20/0.53  fof(f288,plain,(
% 0.20/0.53    k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f60,f285])).
% 0.20/0.53  fof(f331,plain,(
% 0.20/0.53    sK9 = k1_funct_1(k2_funct_1(sK7),k1_funct_1(sK7,sK9))),
% 0.20/0.53    inference(resolution,[],[f312,f286])).
% 0.20/0.53  fof(f286,plain,(
% 0.20/0.53    r2_hidden(sK9,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f250,f285])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    r2_hidden(sK9,k1_xboole_0) | ~v2_funct_1(sK7)),
% 0.20/0.53    inference(backward_demodulation,[],[f59,f245])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (21310)------------------------------
% 0.20/0.53  % (21310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21310)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (21310)Memory used [KB]: 6396
% 0.20/0.53  % (21310)Time elapsed: 0.118 s
% 0.20/0.53  % (21310)------------------------------
% 0.20/0.53  % (21310)------------------------------
% 0.20/0.53  % (21311)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (21306)Success in time 0.17 s
%------------------------------------------------------------------------------
