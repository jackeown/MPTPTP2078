%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 282 expanded)
%              Number of leaves         :   22 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  349 (1365 expanded)
%              Number of equality atoms :   96 ( 383 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(subsumption_resolution,[],[f232,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f232,plain,(
    ~ r1_tarski(k1_xboole_0,k2_relat_1(sK9)) ),
    inference(backward_demodulation,[],[f157,f207])).

fof(f207,plain,(
    k1_xboole_0 = sK8 ),
    inference(subsumption_resolution,[],[f206,f133])).

fof(f133,plain,(
    r2_hidden(sK10(sK11(sK9,sK8)),sK7) ),
    inference(resolution,[],[f122,f60])).

fof(f60,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK8)
      | r2_hidden(sK10(X3),sK7) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK8 != k2_relset_1(sK7,sK8,sK9)
    & ! [X3] :
        ( ( k1_funct_1(sK9,sK10(X3)) = X3
          & r2_hidden(sK10(X3),sK7) )
        | ~ r2_hidden(X3,sK8) )
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    & v1_funct_2(sK9,sK7,sK8)
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f14,f35,f34])).

fof(f34,plain,
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
   => ( sK8 != k2_relset_1(sK7,sK8,sK9)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK9,X4) = X3
              & r2_hidden(X4,sK7) )
          | ~ r2_hidden(X3,sK8) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      & v1_funct_2(sK9,sK7,sK8)
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK9,X4) = X3
          & r2_hidden(X4,sK7) )
     => ( k1_funct_1(sK9,sK10(X3)) = X3
        & r2_hidden(sK10(X3),sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f122,plain,(
    r2_hidden(sK11(sK9,sK8),sK8) ),
    inference(resolution,[],[f121,f84])).

% (11338)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f84,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0)
          & r2_hidden(sK11(X0,X1),X1) ) )
      & ( ! [X4] :
            ( r2_hidden(k4_tarski(sK12(X0,X4),X4),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0)
        & r2_hidden(sK11(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X4,X0] :
      ( ? [X5] : r2_hidden(k4_tarski(X5,X4),X0)
     => r2_hidden(k4_tarski(sK12(X0,X4),X4),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] : r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X2,X1] :
      ( ( sP3(X2,X1)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
        | ~ sP3(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X1] :
      ( sP3(X2,X1)
    <=> ! [X3] :
          ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
          | ~ r2_hidden(X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

% (11331)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f121,plain,(
    ~ sP3(sK9,sK8) ),
    inference(subsumption_resolution,[],[f119,f62])).

fof(f62,plain,(
    sK8 != k2_relset_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,
    ( sK8 = k2_relset_1(sK7,sK8,sK9)
    | ~ sP3(sK9,sK8) ),
    inference(resolution,[],[f108,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X2,X0,X1) = X0
      | ~ sP3(X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP3(X1,X0)
          | k2_relset_1(X2,X0,X1) != X0 )
        & ( k2_relset_1(X2,X0,X1) = X0
          | ~ sP3(X1,X0) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X2,X0] :
      ( ( ( sP3(X2,X1)
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ~ sP3(X2,X1) ) )
      | ~ sP4(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X2,X0] :
      ( ( sP3(X2,X1)
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ sP4(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f108,plain,(
    sP4(sK8,sK9,sK7) ),
    inference(resolution,[],[f59,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP4(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f21,f29,f28])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f59,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f36])).

fof(f206,plain,
    ( ~ r2_hidden(sK10(sK11(sK9,sK8)),sK7)
    | k1_xboole_0 = sK8 ),
    inference(superposition,[],[f204,f165])).

fof(f165,plain,
    ( sK7 = k1_relat_1(sK9)
    | k1_xboole_0 = sK8 ),
    inference(resolution,[],[f144,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f144,plain,
    ( sP0(sK7,sK8)
    | sK7 = k1_relat_1(sK9) ),
    inference(subsumption_resolution,[],[f143,f106])).

fof(f106,plain,(
    sP1(sK7,sK9,sK8) ),
    inference(resolution,[],[f59,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f20,f26,f25,f24])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f143,plain,
    ( sK7 = k1_relat_1(sK9)
    | sP0(sK7,sK8)
    | ~ sP1(sK7,sK9,sK8) ),
    inference(subsumption_resolution,[],[f140,f58])).

fof(f58,plain,(
    v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f140,plain,
    ( sK7 = k1_relat_1(sK9)
    | ~ v1_funct_2(sK9,sK7,sK8)
    | sP0(sK7,sK8)
    | ~ sP1(sK7,sK9,sK8) ),
    inference(superposition,[],[f103,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f103,plain,(
    k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9) ),
    inference(resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f204,plain,(
    ~ r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9)) ),
    inference(subsumption_resolution,[],[f203,f168])).

fof(f168,plain,(
    ! [X1] : ~ sP5(sK11(sK9,sK8),X1,sK9) ),
    inference(subsumption_resolution,[],[f167,f111])).

fof(f111,plain,(
    ! [X0,X1] : sP6(sK9,X0,X1) ),
    inference(subsumption_resolution,[],[f110,f57])).

fof(f57,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f110,plain,(
    ! [X0,X1] :
      ( sP6(sK9,X0,X1)
      | ~ v1_funct_1(sK9) ) ),
    inference(resolution,[],[f102,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( sP6(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f23,f32,f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ( k1_funct_1(X2,X0) = X1
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> sP5(X1,X0,X2) )
      | ~ sP6(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f102,plain,(
    v1_relat_1(sK9) ),
    inference(resolution,[],[f59,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

% (11322)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f167,plain,(
    ! [X1] :
      ( ~ sP5(sK11(sK9,sK8),X1,sK9)
      | ~ sP6(sK9,X1,sK11(sK9,sK8)) ) ),
    inference(resolution,[],[f123,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | ~ sP5(X2,X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X1,X2),X0)
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ sP5(X1,X0,X2) )
        & ( sP5(X1,X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ sP6(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f123,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK11(sK9,sK8)),sK9) ),
    inference(resolution,[],[f121,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( sP3(X0,X1)
      | ~ r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f203,plain,
    ( sP5(sK11(sK9,sK8),sK10(sK11(sK9,sK8)),sK9)
    | ~ r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9)) ),
    inference(superposition,[],[f99,f185])).

fof(f185,plain,(
    sK11(sK9,sK8) = k1_funct_1(sK9,sK10(sK11(sK9,sK8))) ),
    inference(resolution,[],[f139,f121])).

fof(f139,plain,(
    ! [X4] :
      ( sP3(X4,sK8)
      | sK11(X4,sK8) = k1_funct_1(sK9,sK10(sK11(X4,sK8))) ) ),
    inference(resolution,[],[f61,f84])).

fof(f61,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK8)
      | k1_funct_1(sK9,sK10(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X2,X1] :
      ( sP5(k1_funct_1(X2,X1),X1,X2)
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1,X2)
      | k1_funct_1(X2,X1) != X0
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | k1_funct_1(X2,X1) != X0
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f157,plain,(
    ~ r1_tarski(sK8,k2_relat_1(sK9)) ),
    inference(subsumption_resolution,[],[f155,f118])).

fof(f118,plain,(
    sK8 != k2_relat_1(sK9) ),
    inference(subsumption_resolution,[],[f116,f59])).

fof(f116,plain,
    ( sK8 != k2_relat_1(sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(superposition,[],[f62,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

% (11320)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f155,plain,
    ( sK8 = k2_relat_1(sK9)
    | ~ r1_tarski(sK8,k2_relat_1(sK9)) ),
    inference(resolution,[],[f153,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f153,plain,(
    r1_tarski(k2_relat_1(sK9),sK8) ),
    inference(resolution,[],[f152,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f152,plain,(
    m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8)) ),
    inference(subsumption_resolution,[],[f151,f59])).

fof(f151,plain,
    ( m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(superposition,[],[f72,f104])).

fof(f104,plain,(
    k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9) ),
    inference(resolution,[],[f59,f71])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (11317)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (11319)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (11321)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (11335)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (11324)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (11325)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (11327)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (11339)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (11325)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (11318)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f232,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ~r1_tarski(k1_xboole_0,k2_relat_1(sK9))),
% 0.22/0.51    inference(backward_demodulation,[],[f157,f207])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    k1_xboole_0 = sK8),
% 0.22/0.51    inference(subsumption_resolution,[],[f206,f133])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    r2_hidden(sK10(sK11(sK9,sK8)),sK7)),
% 0.22/0.51    inference(resolution,[],[f122,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(X3,sK8) | r2_hidden(sK10(X3),sK7)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    sK8 != k2_relset_1(sK7,sK8,sK9) & ! [X3] : ((k1_funct_1(sK9,sK10(X3)) = X3 & r2_hidden(sK10(X3),sK7)) | ~r2_hidden(X3,sK8)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f14,f35,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK8 != k2_relset_1(sK7,sK8,sK9) & ! [X3] : (? [X4] : (k1_funct_1(sK9,X4) = X3 & r2_hidden(X4,sK7)) | ~r2_hidden(X3,sK8)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X3] : (? [X4] : (k1_funct_1(sK9,X4) = X3 & r2_hidden(X4,sK7)) => (k1_funct_1(sK9,sK10(X3)) = X3 & r2_hidden(sK10(X3),sK7)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f11])).
% 0.22/0.51  fof(f11,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    r2_hidden(sK11(sK9,sK8),sK8)),
% 0.22/0.51    inference(resolution,[],[f121,f84])).
% 0.22/0.51  % (11338)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP3(X0,X1) | r2_hidden(sK11(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP3(X0,X1) | (! [X3] : ~r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0) & r2_hidden(sK11(X0,X1),X1))) & (! [X4] : (r2_hidden(k4_tarski(sK12(X0,X4),X4),X0) | ~r2_hidden(X4,X1)) | ~sP3(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f48,f50,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(X2,X1)) => (! [X3] : ~r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0) & r2_hidden(sK11(X0,X1),X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ! [X4,X0] : (? [X5] : r2_hidden(k4_tarski(X5,X4),X0) => r2_hidden(k4_tarski(sK12(X0,X4),X4),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(X4,X1)) | ~sP3(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X2,X1] : ((sP3(X2,X1) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | ~sP3(X2,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X2,X1] : (sP3(X2,X1) <=> ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.51  % (11331)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ~sP3(sK9,sK8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f119,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    sK8 != k2_relset_1(sK7,sK8,sK9)),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    sK8 = k2_relset_1(sK7,sK8,sK9) | ~sP3(sK9,sK8)),
% 0.22/0.51    inference(resolution,[],[f108,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X2,X0,X1) = X0 | ~sP3(X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((sP3(X1,X0) | k2_relset_1(X2,X0,X1) != X0) & (k2_relset_1(X2,X0,X1) = X0 | ~sP3(X1,X0))) | ~sP4(X0,X1,X2))),
% 0.22/0.51    inference(rectify,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X1,X2,X0] : (((sP3(X2,X1) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ~sP3(X2,X1))) | ~sP4(X1,X2,X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X1,X2,X0] : ((sP3(X2,X1) <=> k2_relset_1(X0,X1,X2) = X1) | ~sP4(X1,X2,X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    sP4(sK8,sK9,sK7)),
% 0.22/0.51    inference(resolution,[],[f59,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (sP4(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (sP4(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(definition_folding,[],[f21,f29,f28])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    ~r2_hidden(sK10(sK11(sK9,sK8)),sK7) | k1_xboole_0 = sK8),
% 0.22/0.52    inference(superposition,[],[f204,f165])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    sK7 = k1_relat_1(sK9) | k1_xboole_0 = sK8),
% 0.22/0.52    inference(resolution,[],[f144,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    sP0(sK7,sK8) | sK7 = k1_relat_1(sK9)),
% 0.22/0.52    inference(subsumption_resolution,[],[f143,f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    sP1(sK7,sK9,sK8)),
% 0.22/0.52    inference(resolution,[],[f59,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(definition_folding,[],[f20,f26,f25,f24])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    sK7 = k1_relat_1(sK9) | sP0(sK7,sK8) | ~sP1(sK7,sK9,sK8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f140,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    v1_funct_2(sK9,sK7,sK8)),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    sK7 = k1_relat_1(sK9) | ~v1_funct_2(sK9,sK7,sK8) | sP0(sK7,sK8) | ~sP1(sK7,sK9,sK8)),
% 0.22/0.52    inference(superposition,[],[f103,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.22/0.52    inference(rectify,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f25])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9)),
% 0.22/0.52    inference(resolution,[],[f59,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    ~r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9))),
% 0.22/0.52    inference(subsumption_resolution,[],[f203,f168])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ( ! [X1] : (~sP5(sK11(sK9,sK8),X1,sK9)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f167,f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP6(sK9,X0,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f110,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v1_funct_1(sK9)),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP6(sK9,X0,X1) | ~v1_funct_1(sK9)) )),
% 0.22/0.52    inference(resolution,[],[f102,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP6(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (sP6(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(definition_folding,[],[f23,f32,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X2,X0,X1] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> sP5(X1,X0,X2)) | ~sP6(X2,X0,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    v1_relat_1(sK9)),
% 0.22/0.52    inference(resolution,[],[f59,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  % (11322)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ( ! [X1] : (~sP5(sK11(sK9,sK8),X1,sK9) | ~sP6(sK9,X1,sK11(sK9,sK8))) )),
% 0.22/0.52    inference(resolution,[],[f123,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | ~sP5(X2,X1,X0) | ~sP6(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X1,X2),X0) | ~sP5(X2,X1,X0)) & (sP5(X2,X1,X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~sP6(X0,X1,X2))),
% 0.22/0.52    inference(rectify,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ! [X2,X0,X1] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~sP6(X2,X0,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f32])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK11(sK9,sK8)),sK9)) )),
% 0.22/0.52    inference(resolution,[],[f121,f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (sP3(X0,X1) | ~r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f51])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    sP5(sK11(sK9,sK8),sK10(sK11(sK9,sK8)),sK9) | ~r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9))),
% 0.22/0.52    inference(superposition,[],[f99,f185])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    sK11(sK9,sK8) = k1_funct_1(sK9,sK10(sK11(sK9,sK8)))),
% 0.22/0.52    inference(resolution,[],[f139,f121])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ( ! [X4] : (sP3(X4,sK8) | sK11(X4,sK8) = k1_funct_1(sK9,sK10(sK11(X4,sK8)))) )),
% 0.22/0.52    inference(resolution,[],[f61,f84])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X3] : (~r2_hidden(X3,sK8) | k1_funct_1(sK9,sK10(X3)) = X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X2,X1] : (sP5(k1_funct_1(X2,X1),X1,X2) | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 0.22/0.52    inference(equality_resolution,[],[f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP5(X0,X1,X2) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | ~sP5(X0,X1,X2)))),
% 0.22/0.52    inference(rectify,[],[f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP5(X1,X0,X2)))),
% 0.22/0.52    inference(flattening,[],[f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP5(X1,X0,X2)))),
% 0.22/0.52    inference(nnf_transformation,[],[f31])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ~r1_tarski(sK8,k2_relat_1(sK9))),
% 0.22/0.52    inference(subsumption_resolution,[],[f155,f118])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    sK8 != k2_relat_1(sK9)),
% 0.22/0.52    inference(subsumption_resolution,[],[f116,f59])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    sK8 != k2_relat_1(sK9) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 0.22/0.52    inference(superposition,[],[f62,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  % (11320)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    sK8 = k2_relat_1(sK9) | ~r1_tarski(sK8,k2_relat_1(sK9))),
% 0.22/0.52    inference(resolution,[],[f153,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK9),sK8)),
% 0.22/0.52    inference(resolution,[],[f152,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8))),
% 0.22/0.52    inference(subsumption_resolution,[],[f151,f59])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK8)) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 0.22/0.52    inference(superposition,[],[f72,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9)),
% 0.22/0.52    inference(resolution,[],[f59,f71])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (11325)------------------------------
% 0.22/0.52  % (11325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11325)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (11325)Memory used [KB]: 1791
% 0.22/0.52  % (11325)Time elapsed: 0.099 s
% 0.22/0.52  % (11325)------------------------------
% 0.22/0.52  % (11325)------------------------------
% 0.22/0.52  % (11316)Success in time 0.153 s
%------------------------------------------------------------------------------
