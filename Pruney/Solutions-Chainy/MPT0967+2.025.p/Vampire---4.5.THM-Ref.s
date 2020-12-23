%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:46 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  119 (13998 expanded)
%              Number of leaves         :   14 (3434 expanded)
%              Depth                    :   31
%              Number of atoms          :  375 (81911 expanded)
%              Number of equality atoms :  107 (17601 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(subsumption_resolution,[],[f249,f210])).

fof(f210,plain,(
    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f191,f190])).

fof(f190,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f43,f189])).

fof(f189,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f174,f82])).

fof(f82,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f174,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f42,f170])).

fof(f170,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f75,f158,f169])).

fof(f169,plain,
    ( k1_xboole_0 = sK3
    | v1_funct_2(sK4,sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f165,f159])).

fof(f159,plain,
    ( sK1 = k1_relset_1(sK1,sK3,sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f140,f150])).

fof(f150,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f149,f94])).

fof(f94,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f59,f41])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f149,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f147,f90])).

fof(f90,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f65,f41])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f9])).

% (17567)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f9,axiom,(
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

fof(f147,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f140,plain,(
    k1_relat_1(sK4) = k1_relset_1(k1_relat_1(sK4),sK3,sK4) ),
    inference(resolution,[],[f139,f59])).

fof(f139,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(subsumption_resolution,[],[f138,f79])).

fof(f79,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f76,f41])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f46,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f138,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f137,f89])).

fof(f89,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f60,f41])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f137,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f124,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f124,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(resolution,[],[f121,f103])).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK3)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK3)
      | ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f100,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

% (17578)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f100,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK5(X10,X11),sK3)
      | r1_tarski(X10,X11)
      | ~ r1_tarski(X10,sK2) ) ),
    inference(resolution,[],[f92,f42])).

fof(f92,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK5(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f88,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f56,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ) ),
    inference(subsumption_resolution,[],[f120,f79])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f165,plain,
    ( sK1 != k1_relset_1(sK1,sK3,sK4)
    | k1_xboole_0 = sK3
    | v1_funct_2(sK4,sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f63,f160])).

fof(f160,plain,
    ( sP0(sK1,sK4,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f141,f150])).

fof(f141,plain,(
    sP0(k1_relat_1(sK4),sK4,sK3) ),
    inference(resolution,[],[f139,f65])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 = X2
      | v1_funct_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f158,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f139,f150])).

fof(f75,plain,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f44,f39])).

fof(f44,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

% (17573)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f43,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f191,plain,(
    v1_funct_2(sK4,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f40,f189])).

fof(f249,plain,(
    ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f241,f242])).

fof(f242,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f237,f241])).

fof(f237,plain,
    ( v1_funct_2(sK4,k1_xboole_0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(backward_demodulation,[],[f173,f234])).

fof(f234,plain,(
    k1_xboole_0 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f214,f233])).

fof(f233,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(subsumption_resolution,[],[f231,f210])).

fof(f231,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(resolution,[],[f213,f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ sP0(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f213,plain,(
    sP0(k1_xboole_0,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f196,f190])).

fof(f196,plain,(
    sP0(sK1,sK4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f90,f189])).

fof(f214,plain,(
    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(forward_demodulation,[],[f197,f190])).

fof(f197,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f94,f189])).

fof(f173,plain,
    ( k1_xboole_0 = sK3
    | v1_funct_2(sK4,k1_relat_1(sK4),sK3) ),
    inference(subsumption_resolution,[],[f168,f140])).

fof(f168,plain,
    ( k1_relat_1(sK4) != k1_relset_1(k1_relat_1(sK4),sK3,sK4)
    | k1_xboole_0 = sK3
    | v1_funct_2(sK4,k1_relat_1(sK4),sK3) ),
    inference(resolution,[],[f63,f141])).

fof(f241,plain,(
    ~ v1_funct_2(sK4,k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f209,f240])).

fof(f240,plain,(
    ! [X0] : m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(backward_demodulation,[],[f223,f234])).

fof(f223,plain,(
    ! [X0] : m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
    inference(subsumption_resolution,[],[f217,f45])).

fof(f217,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ) ),
    inference(backward_demodulation,[],[f121,f216])).

fof(f216,plain,(
    k1_xboole_0 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f215,f45])).

fof(f215,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK4))
    | k1_xboole_0 = k2_relat_1(sK4) ),
    inference(forward_demodulation,[],[f198,f189])).

fof(f198,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | ~ r1_tarski(sK2,k2_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f96,f189])).

fof(f96,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK4))
    | sK2 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f95,f79])).

fof(f95,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f83,f89])).

fof(f83,plain,(
    ! [X2,X3] :
      ( ~ v5_relat_1(X3,X2)
      | k2_relat_1(X3) = X2
      | ~ r1_tarski(X2,k2_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f55,f48])).

fof(f209,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) ),
    inference(forward_demodulation,[],[f208,f190])).

fof(f208,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(backward_demodulation,[],[f75,f190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (17568)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.52  % (17572)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.53  % (17564)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.53  % (17571)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.53  % (17566)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (17591)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.53  % (17576)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (17580)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.28/0.54  % (17579)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.54  % (17583)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.54  % (17569)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.54  % (17584)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.54  % (17571)Refutation found. Thanks to Tanya!
% 1.28/0.54  % SZS status Theorem for theBenchmark
% 1.28/0.54  % (17586)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.54  % (17569)Refutation not found, incomplete strategy% (17569)------------------------------
% 1.28/0.54  % (17569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (17569)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (17590)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.54  % (17569)Memory used [KB]: 6268
% 1.28/0.54  % (17569)Time elapsed: 0.133 s
% 1.28/0.54  % (17569)------------------------------
% 1.28/0.54  % (17569)------------------------------
% 1.28/0.54  % (17565)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % SZS output start Proof for theBenchmark
% 1.28/0.54  fof(f252,plain,(
% 1.28/0.54    $false),
% 1.28/0.54    inference(subsumption_resolution,[],[f249,f210])).
% 1.28/0.54  fof(f210,plain,(
% 1.28/0.54    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 1.28/0.54    inference(forward_demodulation,[],[f191,f190])).
% 1.28/0.54  fof(f190,plain,(
% 1.28/0.54    k1_xboole_0 = sK1),
% 1.28/0.54    inference(subsumption_resolution,[],[f43,f189])).
% 1.28/0.54  fof(f189,plain,(
% 1.28/0.54    k1_xboole_0 = sK2),
% 1.28/0.54    inference(subsumption_resolution,[],[f174,f82])).
% 1.28/0.54  fof(f82,plain,(
% 1.28/0.54    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.28/0.54    inference(resolution,[],[f55,f45])).
% 1.28/0.54  fof(f45,plain,(
% 1.28/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f3])).
% 1.28/0.54  fof(f3,axiom,(
% 1.28/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.28/0.54  fof(f55,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.28/0.54    inference(cnf_transformation,[],[f31])).
% 1.28/0.54  fof(f31,plain,(
% 1.28/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.54    inference(flattening,[],[f30])).
% 1.28/0.54  fof(f30,plain,(
% 1.28/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.54    inference(nnf_transformation,[],[f2])).
% 1.28/0.54  fof(f2,axiom,(
% 1.28/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.28/0.54  fof(f174,plain,(
% 1.28/0.54    r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2),
% 1.28/0.54    inference(superposition,[],[f42,f170])).
% 1.28/0.54  fof(f170,plain,(
% 1.28/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 1.28/0.54    inference(global_subsumption,[],[f75,f158,f169])).
% 1.28/0.54  fof(f169,plain,(
% 1.28/0.54    k1_xboole_0 = sK3 | v1_funct_2(sK4,sK1,sK3) | k1_xboole_0 = sK2),
% 1.28/0.54    inference(subsumption_resolution,[],[f165,f159])).
% 1.28/0.54  fof(f159,plain,(
% 1.28/0.54    sK1 = k1_relset_1(sK1,sK3,sK4) | k1_xboole_0 = sK2),
% 1.28/0.54    inference(superposition,[],[f140,f150])).
% 1.28/0.54  fof(f150,plain,(
% 1.28/0.54    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 1.28/0.54    inference(superposition,[],[f149,f94])).
% 1.28/0.54  fof(f94,plain,(
% 1.28/0.54    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 1.28/0.54    inference(resolution,[],[f59,f41])).
% 1.28/0.54  fof(f41,plain,(
% 1.28/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.28/0.54    inference(cnf_transformation,[],[f28])).
% 1.28/0.54  fof(f28,plain,(
% 1.28/0.54    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f27])).
% 1.28/0.54  fof(f27,plain,(
% 1.28/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f15,plain,(
% 1.28/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.28/0.54    inference(flattening,[],[f14])).
% 1.28/0.54  fof(f14,plain,(
% 1.28/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.28/0.54    inference(ennf_transformation,[],[f12])).
% 1.28/0.54  fof(f12,negated_conjecture,(
% 1.28/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.28/0.54    inference(negated_conjecture,[],[f11])).
% 1.28/0.54  fof(f11,conjecture,(
% 1.28/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 1.28/0.54  fof(f59,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f21])).
% 1.28/0.54  fof(f21,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f8])).
% 1.28/0.54  fof(f8,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.28/0.54  fof(f149,plain,(
% 1.28/0.54    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 1.28/0.54    inference(subsumption_resolution,[],[f147,f90])).
% 1.28/0.54  fof(f90,plain,(
% 1.28/0.54    sP0(sK1,sK4,sK2)),
% 1.28/0.54    inference(resolution,[],[f65,f41])).
% 1.28/0.54  fof(f65,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f38])).
% 1.28/0.54  fof(f38,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(nnf_transformation,[],[f26])).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(definition_folding,[],[f24,f25])).
% 1.28/0.54  fof(f25,plain,(
% 1.28/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.28/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.28/0.54  fof(f24,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(flattening,[],[f23])).
% 1.28/0.54  fof(f23,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f9])).
% 1.28/0.54  % (17567)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  fof(f9,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.28/0.54  fof(f147,plain,(
% 1.28/0.54    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2 | ~sP0(sK1,sK4,sK2)),
% 1.28/0.54    inference(resolution,[],[f61,f40])).
% 1.28/0.54  fof(f40,plain,(
% 1.28/0.54    v1_funct_2(sK4,sK1,sK2)),
% 1.28/0.54    inference(cnf_transformation,[],[f28])).
% 1.28/0.54  fof(f61,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f37])).
% 1.28/0.54  fof(f37,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.28/0.54    inference(rectify,[],[f36])).
% 1.28/0.54  fof(f36,plain,(
% 1.28/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.28/0.54    inference(nnf_transformation,[],[f25])).
% 1.28/0.54  fof(f140,plain,(
% 1.28/0.54    k1_relat_1(sK4) = k1_relset_1(k1_relat_1(sK4),sK3,sK4)),
% 1.28/0.54    inference(resolution,[],[f139,f59])).
% 1.28/0.54  fof(f139,plain,(
% 1.28/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 1.28/0.54    inference(subsumption_resolution,[],[f138,f79])).
% 1.28/0.54  fof(f79,plain,(
% 1.28/0.54    v1_relat_1(sK4)),
% 1.28/0.54    inference(resolution,[],[f76,f41])).
% 1.28/0.54  fof(f76,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.28/0.54    inference(resolution,[],[f46,f47])).
% 1.28/0.54  fof(f47,plain,(
% 1.28/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f6])).
% 1.28/0.54  fof(f6,axiom,(
% 1.28/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.28/0.54  fof(f46,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f16])).
% 1.28/0.54  fof(f16,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f4])).
% 1.28/0.54  fof(f4,axiom,(
% 1.28/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.28/0.54  fof(f138,plain,(
% 1.28/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_relat_1(sK4)),
% 1.28/0.54    inference(subsumption_resolution,[],[f137,f89])).
% 1.28/0.54  fof(f89,plain,(
% 1.28/0.54    v5_relat_1(sK4,sK2)),
% 1.28/0.54    inference(resolution,[],[f60,f41])).
% 1.28/0.54  fof(f60,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f22])).
% 1.28/0.54  fof(f22,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f13])).
% 1.28/0.54  fof(f13,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.28/0.54    inference(pure_predicate_removal,[],[f7])).
% 1.28/0.54  fof(f7,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.28/0.54  fof(f137,plain,(
% 1.28/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v5_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 1.28/0.54    inference(resolution,[],[f124,f48])).
% 1.28/0.54  fof(f48,plain,(
% 1.28/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f29])).
% 1.28/0.54  fof(f29,plain,(
% 1.28/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.28/0.54    inference(nnf_transformation,[],[f17])).
% 1.28/0.54  fof(f17,plain,(
% 1.28/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.28/0.54    inference(ennf_transformation,[],[f5])).
% 1.28/0.54  fof(f5,axiom,(
% 1.28/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.28/0.54  fof(f124,plain,(
% 1.28/0.54    ~r1_tarski(k2_relat_1(sK4),sK2) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 1.28/0.54    inference(resolution,[],[f121,f103])).
% 1.28/0.54  fof(f103,plain,(
% 1.28/0.54    ( ! [X0] : (r1_tarski(X0,sK3) | ~r1_tarski(X0,sK2)) )),
% 1.28/0.54    inference(duplicate_literal_removal,[],[f101])).
% 1.28/0.54  fof(f101,plain,(
% 1.28/0.54    ( ! [X0] : (r1_tarski(X0,sK3) | ~r1_tarski(X0,sK2) | r1_tarski(X0,sK3)) )),
% 1.28/0.54    inference(resolution,[],[f100,f58])).
% 1.28/0.54  fof(f58,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f35])).
% 1.28/0.54  % (17578)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.54  fof(f35,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 1.28/0.54  fof(f34,plain,(
% 1.28/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f33,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(rectify,[],[f32])).
% 1.28/0.54  fof(f32,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(nnf_transformation,[],[f20])).
% 1.28/0.54  fof(f20,plain,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f1])).
% 1.28/0.54  fof(f1,axiom,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.28/0.54  fof(f100,plain,(
% 1.28/0.54    ( ! [X10,X11] : (r2_hidden(sK5(X10,X11),sK3) | r1_tarski(X10,X11) | ~r1_tarski(X10,sK2)) )),
% 1.28/0.54    inference(resolution,[],[f92,f42])).
% 1.28/0.54  fof(f92,plain,(
% 1.28/0.54    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK5(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 1.28/0.54    inference(resolution,[],[f88,f56])).
% 1.28/0.54  fof(f56,plain,(
% 1.28/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f35])).
% 1.28/0.54  fof(f88,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(resolution,[],[f56,f57])).
% 1.28/0.54  fof(f57,plain,(
% 1.28/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f35])).
% 1.28/0.54  fof(f121,plain,(
% 1.28/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f120,f79])).
% 1.28/0.54  fof(f120,plain,(
% 1.28/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) | ~v1_relat_1(sK4)) )),
% 1.28/0.54    inference(resolution,[],[f52,f39])).
% 1.28/0.54  fof(f39,plain,(
% 1.28/0.54    v1_funct_1(sK4)),
% 1.28/0.54    inference(cnf_transformation,[],[f28])).
% 1.28/0.54  fof(f52,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  fof(f19,plain,(
% 1.28/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.28/0.54    inference(flattening,[],[f18])).
% 1.28/0.54  fof(f18,plain,(
% 1.28/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.28/0.54    inference(ennf_transformation,[],[f10])).
% 1.28/0.54  fof(f10,axiom,(
% 1.28/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.28/0.54  fof(f165,plain,(
% 1.28/0.54    sK1 != k1_relset_1(sK1,sK3,sK4) | k1_xboole_0 = sK3 | v1_funct_2(sK4,sK1,sK3) | k1_xboole_0 = sK2),
% 1.28/0.54    inference(resolution,[],[f63,f160])).
% 1.28/0.54  fof(f160,plain,(
% 1.28/0.54    sP0(sK1,sK4,sK3) | k1_xboole_0 = sK2),
% 1.28/0.54    inference(superposition,[],[f141,f150])).
% 1.28/0.54  fof(f141,plain,(
% 1.28/0.54    sP0(k1_relat_1(sK4),sK4,sK3)),
% 1.28/0.54    inference(resolution,[],[f139,f65])).
% 1.28/0.54  fof(f63,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 = X2 | v1_funct_2(X1,X0,X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f37])).
% 1.28/0.54  fof(f158,plain,(
% 1.28/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | k1_xboole_0 = sK2),
% 1.28/0.54    inference(superposition,[],[f139,f150])).
% 1.28/0.54  fof(f75,plain,(
% 1.28/0.54    ~v1_funct_2(sK4,sK1,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.28/0.54    inference(subsumption_resolution,[],[f44,f39])).
% 1.28/0.54  fof(f44,plain,(
% 1.28/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 1.28/0.54    inference(cnf_transformation,[],[f28])).
% 1.28/0.54  fof(f42,plain,(
% 1.28/0.54    r1_tarski(sK2,sK3)),
% 1.28/0.54    inference(cnf_transformation,[],[f28])).
% 1.28/0.54  % (17573)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.54  fof(f43,plain,(
% 1.28/0.54    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.28/0.54    inference(cnf_transformation,[],[f28])).
% 1.28/0.54  fof(f191,plain,(
% 1.28/0.54    v1_funct_2(sK4,sK1,k1_xboole_0)),
% 1.28/0.54    inference(backward_demodulation,[],[f40,f189])).
% 1.28/0.54  fof(f249,plain,(
% 1.28/0.54    ~v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 1.28/0.54    inference(backward_demodulation,[],[f241,f242])).
% 1.28/0.54  fof(f242,plain,(
% 1.28/0.54    k1_xboole_0 = sK3),
% 1.28/0.54    inference(subsumption_resolution,[],[f237,f241])).
% 1.28/0.54  fof(f237,plain,(
% 1.28/0.54    v1_funct_2(sK4,k1_xboole_0,sK3) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(backward_demodulation,[],[f173,f234])).
% 1.28/0.54  fof(f234,plain,(
% 1.28/0.54    k1_xboole_0 = k1_relat_1(sK4)),
% 1.28/0.54    inference(backward_demodulation,[],[f214,f233])).
% 1.28/0.54  fof(f233,plain,(
% 1.28/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 1.28/0.54    inference(subsumption_resolution,[],[f231,f210])).
% 1.28/0.54  fof(f231,plain,(
% 1.28/0.54    ~v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 1.28/0.54    inference(resolution,[],[f213,f71])).
% 1.28/0.54  fof(f71,plain,(
% 1.28/0.54    ( ! [X2,X1] : (~sP0(k1_xboole_0,X1,X2) | ~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)) )),
% 1.28/0.54    inference(equality_resolution,[],[f62])).
% 1.28/0.54  fof(f62,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f37])).
% 1.28/0.54  fof(f213,plain,(
% 1.28/0.54    sP0(k1_xboole_0,sK4,k1_xboole_0)),
% 1.28/0.54    inference(forward_demodulation,[],[f196,f190])).
% 1.28/0.54  fof(f196,plain,(
% 1.28/0.54    sP0(sK1,sK4,k1_xboole_0)),
% 1.28/0.54    inference(backward_demodulation,[],[f90,f189])).
% 1.28/0.54  fof(f214,plain,(
% 1.28/0.54    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 1.28/0.54    inference(forward_demodulation,[],[f197,f190])).
% 1.28/0.54  fof(f197,plain,(
% 1.28/0.54    k1_relat_1(sK4) = k1_relset_1(sK1,k1_xboole_0,sK4)),
% 1.28/0.54    inference(backward_demodulation,[],[f94,f189])).
% 1.28/0.54  fof(f173,plain,(
% 1.28/0.54    k1_xboole_0 = sK3 | v1_funct_2(sK4,k1_relat_1(sK4),sK3)),
% 1.28/0.54    inference(subsumption_resolution,[],[f168,f140])).
% 1.28/0.54  fof(f168,plain,(
% 1.28/0.54    k1_relat_1(sK4) != k1_relset_1(k1_relat_1(sK4),sK3,sK4) | k1_xboole_0 = sK3 | v1_funct_2(sK4,k1_relat_1(sK4),sK3)),
% 1.28/0.54    inference(resolution,[],[f63,f141])).
% 1.28/0.54  fof(f241,plain,(
% 1.28/0.54    ~v1_funct_2(sK4,k1_xboole_0,sK3)),
% 1.28/0.54    inference(subsumption_resolution,[],[f209,f240])).
% 1.28/0.54  fof(f240,plain,(
% 1.28/0.54    ( ! [X0] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 1.28/0.54    inference(backward_demodulation,[],[f223,f234])).
% 1.28/0.54  fof(f223,plain,(
% 1.28/0.54    ( ! [X0] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f217,f45])).
% 1.28/0.54  fof(f217,plain,(
% 1.28/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))) )),
% 1.28/0.54    inference(backward_demodulation,[],[f121,f216])).
% 1.28/0.54  fof(f216,plain,(
% 1.28/0.54    k1_xboole_0 = k2_relat_1(sK4)),
% 1.28/0.54    inference(subsumption_resolution,[],[f215,f45])).
% 1.28/0.54  fof(f215,plain,(
% 1.28/0.54    ~r1_tarski(k1_xboole_0,k2_relat_1(sK4)) | k1_xboole_0 = k2_relat_1(sK4)),
% 1.28/0.54    inference(forward_demodulation,[],[f198,f189])).
% 1.28/0.54  fof(f198,plain,(
% 1.28/0.54    k1_xboole_0 = k2_relat_1(sK4) | ~r1_tarski(sK2,k2_relat_1(sK4))),
% 1.28/0.54    inference(backward_demodulation,[],[f96,f189])).
% 1.28/0.54  fof(f96,plain,(
% 1.28/0.54    ~r1_tarski(sK2,k2_relat_1(sK4)) | sK2 = k2_relat_1(sK4)),
% 1.28/0.54    inference(subsumption_resolution,[],[f95,f79])).
% 1.28/0.54  fof(f95,plain,(
% 1.28/0.54    sK2 = k2_relat_1(sK4) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.28/0.54    inference(resolution,[],[f83,f89])).
% 1.28/0.54  fof(f83,plain,(
% 1.28/0.54    ( ! [X2,X3] : (~v5_relat_1(X3,X2) | k2_relat_1(X3) = X2 | ~r1_tarski(X2,k2_relat_1(X3)) | ~v1_relat_1(X3)) )),
% 1.28/0.54    inference(resolution,[],[f55,f48])).
% 1.28/0.54  fof(f209,plain,(
% 1.28/0.54    ~v1_funct_2(sK4,k1_xboole_0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))),
% 1.28/0.54    inference(forward_demodulation,[],[f208,f190])).
% 1.28/0.54  fof(f208,plain,(
% 1.28/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) | ~v1_funct_2(sK4,sK1,sK3)),
% 1.28/0.54    inference(backward_demodulation,[],[f75,f190])).
% 1.28/0.54  % SZS output end Proof for theBenchmark
% 1.28/0.54  % (17571)------------------------------
% 1.28/0.54  % (17571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (17571)Termination reason: Refutation
% 1.28/0.54  
% 1.28/0.54  % (17571)Memory used [KB]: 6396
% 1.28/0.54  % (17571)Time elapsed: 0.122 s
% 1.28/0.54  % (17571)------------------------------
% 1.28/0.54  % (17571)------------------------------
% 1.28/0.54  % (17563)Success in time 0.186 s
%------------------------------------------------------------------------------
