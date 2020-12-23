%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:13 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  196 (1653 expanded)
%              Number of leaves         :   25 ( 417 expanded)
%              Depth                    :   21
%              Number of atoms          :  617 (9805 expanded)
%              Number of equality atoms :  137 (2197 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f722,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f120,f199,f227,f242,f257,f286,f289,f400,f414,f425,f515,f694])).

fof(f694,plain,
    ( spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | spl6_14 ),
    inference(subsumption_resolution,[],[f692,f609])).

fof(f609,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | spl6_14 ),
    inference(backward_demodulation,[],[f483,f584])).

fof(f584,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | spl6_14 ),
    inference(subsumption_resolution,[],[f583,f550])).

fof(f550,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ spl6_4
    | ~ spl6_5
    | spl6_14 ),
    inference(superposition,[],[f527,f520])).

fof(f520,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f519,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f519,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f304,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f304,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f53,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

% (4086)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (4078)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f527,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_4
    | ~ spl6_5
    | spl6_14 ),
    inference(forward_demodulation,[],[f526,f119])).

fof(f526,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl6_4
    | spl6_14 ),
    inference(forward_demodulation,[],[f240,f114])).

fof(f240,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl6_14
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f583,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f577,f518])).

fof(f518,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f321,f114])).

fof(f321,plain,(
    v1_funct_2(sK3,k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f320,f131])).

fof(f131,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f53,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f320,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f316,f51])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f316,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f159,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f159,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f158,f131])).

fof(f158,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f133,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f133,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f53,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f577,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(resolution,[],[f540,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f540,plain,
    ( ! [X1] : m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f539,f131])).

fof(f539,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))
        | ~ v1_relat_1(sK3) )
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f538,f51])).

fof(f538,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f533,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f533,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(superposition,[],[f65,f467])).

fof(f467,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f179,f114])).

fof(f179,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl6_11
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f483,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f435,f114])).

fof(f435,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f52,f119])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f692,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | spl6_14 ),
    inference(forward_demodulation,[],[f621,f636])).

fof(f636,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | spl6_14 ),
    inference(subsumption_resolution,[],[f635,f58])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k7_relat_1(k1_xboole_0,X0))
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | spl6_14 ),
    inference(forward_demodulation,[],[f589,f584])).

fof(f589,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | ~ r1_tarski(sK3,k7_relat_1(sK3,X0)) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | spl6_14 ),
    inference(backward_demodulation,[],[f181,f584])).

fof(f181,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,k7_relat_1(sK3,X0))
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f157,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f157,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(resolution,[],[f131,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f621,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | spl6_14 ),
    inference(backward_demodulation,[],[f513,f584])).

fof(f513,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f512,f484])).

fof(f484,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,X0)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f438,f114])).

fof(f438,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(k1_xboole_0,sK1,sK3,X0)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f142,f119])).

fof(f142,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f136,f51])).

fof(f136,plain,(
    ! [X0] :
      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f53,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f512,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f511,f119])).

fof(f511,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f510,f437])).

fof(f437,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(backward_demodulation,[],[f129,f119])).

fof(f129,plain,
    ( sK0 = sK2
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f510,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0)
    | spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f106,f114])).

fof(f106,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f515,plain,
    ( spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f513,f478])).

fof(f478,plain,
    ( v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f378,f114])).

fof(f378,plain,
    ( v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | ~ spl6_14 ),
    inference(superposition,[],[f208,f347])).

fof(f347,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl6_14 ),
    inference(resolution,[],[f315,f58])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f314,f131])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl6_14 ),
    inference(superposition,[],[f60,f297])).

fof(f297,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f132,f241])).

fof(f241,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f239])).

fof(f132,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f53,f76])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f208,plain,(
    ! [X0] : v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f207,f182])).

fof(f182,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f147,f75])).

fof(f147,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f146,f142])).

fof(f146,plain,(
    ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f137,f51])).

fof(f137,plain,(
    ! [X1] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f53,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f207,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f203,f196])).

fof(f196,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f195,f51])).

fof(f195,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f194,f53])).

fof(f194,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK3,X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f86,f142])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f203,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f202,f64])).

fof(f202,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f201,f182])).

fof(f201,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f184,f61])).

fof(f184,plain,(
    ! [X2] : v5_relat_1(k7_relat_1(sK3,X2),sK1) ),
    inference(resolution,[],[f147,f77])).

fof(f425,plain,
    ( ~ spl6_10
    | spl6_11 ),
    inference(avatar_split_clause,[],[f319,f177,f173])).

fof(f173,plain,
    ( spl6_10
  <=> r1_tarski(sK1,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f319,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ r1_tarski(sK1,k2_relat_1(sK3)) ),
    inference(resolution,[],[f159,f68])).

fof(f414,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f301,f127,f123])).

fof(f123,plain,
    ( spl6_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f301,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f54,f68])).

fof(f54,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f400,plain,
    ( spl6_3
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | spl6_3
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f393,f145])).

fof(f145,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(backward_demodulation,[],[f110,f142])).

fof(f110,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f393,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_14 ),
    inference(superposition,[],[f210,f346])).

fof(f346,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl6_14 ),
    inference(resolution,[],[f315,f54])).

fof(f210,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) ),
    inference(subsumption_resolution,[],[f209,f182])).

fof(f209,plain,(
    ! [X1] :
      ( m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))
      | ~ v1_relat_1(k7_relat_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f204,f196])).

fof(f204,plain,(
    ! [X1] :
      ( m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))
      | ~ v1_funct_1(k7_relat_1(sK3,X1))
      | ~ v1_relat_1(k7_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f202,f65])).

fof(f289,plain,
    ( ~ spl6_4
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl6_4
    | spl6_10 ),
    inference(subsumption_resolution,[],[f272,f58])).

fof(f272,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | ~ spl6_4
    | spl6_10 ),
    inference(backward_demodulation,[],[f175,f114])).

fof(f175,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK3))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f173])).

fof(f286,plain,
    ( spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f284,f258])).

fof(f258,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f250,f91])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f250,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f147,f119])).

fof(f284,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f268,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f268,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | spl6_3
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f145,f114])).

fof(f257,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl6_5
    | spl6_6 ),
    inference(subsumption_resolution,[],[f246,f58])).

fof(f246,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_5
    | spl6_6 ),
    inference(backward_demodulation,[],[f125,f119])).

fof(f125,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f242,plain,
    ( spl6_14
    | spl6_4 ),
    inference(avatar_split_clause,[],[f139,f113,f239])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f134,f52])).

fof(f134,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f227,plain,
    ( spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f223,f144])).

fof(f144,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl6_2 ),
    inference(backward_demodulation,[],[f106,f142])).

fof(f223,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl6_4 ),
    inference(superposition,[],[f208,f211])).

fof(f211,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | spl6_4 ),
    inference(resolution,[],[f161,f54])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f160,f131])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | spl6_4 ),
    inference(superposition,[],[f60,f141])).

fof(f141,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl6_4 ),
    inference(backward_demodulation,[],[f132,f140])).

fof(f140,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f139,f115])).

fof(f115,plain,
    ( k1_xboole_0 != sK1
    | spl6_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f199,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f196,f143])).

fof(f143,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl6_1 ),
    inference(backward_demodulation,[],[f102,f142])).

fof(f102,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f120,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f55,f117,f113])).

fof(f55,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f111,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f56,f108,f104,f100])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (4060)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (4059)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (4065)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (4064)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (4073)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.53/0.57  % (4061)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.57  % (4084)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.59  % (4083)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.59  % (4075)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.59  % (4068)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.82/0.59  % (4081)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.82/0.59  % (4063)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.82/0.59  % (4062)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.82/0.60  % (4071)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.82/0.60  % (4070)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.82/0.60  % (4067)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.82/0.60  % (4069)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.82/0.60  % (4088)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.82/0.60  % (4082)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.82/0.61  % (4077)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.82/0.61  % (4085)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.82/0.61  % (4080)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.82/0.61  % (4087)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.82/0.61  % (4074)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.82/0.62  % (4079)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.82/0.62  % (4072)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.82/0.62  % (4081)Refutation not found, incomplete strategy% (4081)------------------------------
% 1.82/0.62  % (4081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (4081)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.62  
% 1.82/0.62  % (4081)Memory used [KB]: 10874
% 1.82/0.62  % (4081)Time elapsed: 0.194 s
% 1.82/0.62  % (4081)------------------------------
% 1.82/0.62  % (4081)------------------------------
% 1.82/0.62  % (4066)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.82/0.63  % (4076)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.82/0.63  % (4067)Refutation found. Thanks to Tanya!
% 1.82/0.63  % SZS status Theorem for theBenchmark
% 1.82/0.63  % SZS output start Proof for theBenchmark
% 1.82/0.63  fof(f722,plain,(
% 1.82/0.63    $false),
% 1.82/0.63    inference(avatar_sat_refutation,[],[f111,f120,f199,f227,f242,f257,f286,f289,f400,f414,f425,f515,f694])).
% 1.82/0.63  fof(f694,plain,(
% 1.82/0.63    spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | spl6_14),
% 1.82/0.63    inference(avatar_contradiction_clause,[],[f693])).
% 1.82/0.63  fof(f693,plain,(
% 1.82/0.63    $false | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | spl6_14)),
% 1.82/0.63    inference(subsumption_resolution,[],[f692,f609])).
% 1.82/0.63  fof(f609,plain,(
% 1.82/0.63    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_11 | spl6_14)),
% 1.82/0.63    inference(backward_demodulation,[],[f483,f584])).
% 1.82/0.63  fof(f584,plain,(
% 1.82/0.63    k1_xboole_0 = sK3 | (~spl6_4 | ~spl6_5 | ~spl6_11 | spl6_14)),
% 1.82/0.63    inference(subsumption_resolution,[],[f583,f550])).
% 1.82/0.63  fof(f550,plain,(
% 1.82/0.63    k1_xboole_0 != k1_relat_1(sK3) | (~spl6_4 | ~spl6_5 | spl6_14)),
% 1.82/0.63    inference(superposition,[],[f527,f520])).
% 1.82/0.63  fof(f520,plain,(
% 1.82/0.63    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_4 | ~spl6_5)),
% 1.82/0.63    inference(forward_demodulation,[],[f519,f119])).
% 1.82/0.63  fof(f119,plain,(
% 1.82/0.63    k1_xboole_0 = sK0 | ~spl6_5),
% 1.82/0.63    inference(avatar_component_clause,[],[f117])).
% 1.82/0.63  fof(f117,plain,(
% 1.82/0.63    spl6_5 <=> k1_xboole_0 = sK0),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.82/0.63  fof(f519,plain,(
% 1.82/0.63    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl6_4),
% 1.82/0.63    inference(forward_demodulation,[],[f304,f114])).
% 1.82/0.63  fof(f114,plain,(
% 1.82/0.63    k1_xboole_0 = sK1 | ~spl6_4),
% 1.82/0.63    inference(avatar_component_clause,[],[f113])).
% 1.82/0.63  fof(f113,plain,(
% 1.82/0.63    spl6_4 <=> k1_xboole_0 = sK1),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.82/0.63  fof(f304,plain,(
% 1.82/0.63    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.82/0.63    inference(resolution,[],[f53,f76])).
% 1.82/0.63  fof(f76,plain,(
% 1.82/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f30])).
% 1.82/0.63  fof(f30,plain,(
% 1.82/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.63    inference(ennf_transformation,[],[f12])).
% 1.82/0.63  fof(f12,axiom,(
% 1.82/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.82/0.63  fof(f53,plain,(
% 1.82/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.82/0.63    inference(cnf_transformation,[],[f40])).
% 1.82/0.63  fof(f40,plain,(
% 1.82/0.63    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.82/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f39])).
% 1.82/0.63  fof(f39,plain,(
% 1.82/0.63    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.82/0.63    introduced(choice_axiom,[])).
% 1.82/0.63  fof(f21,plain,(
% 1.82/0.63    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.82/0.63    inference(flattening,[],[f20])).
% 1.82/0.63  fof(f20,plain,(
% 1.82/0.63    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.82/0.63    inference(ennf_transformation,[],[f18])).
% 1.82/0.63  fof(f18,negated_conjecture,(
% 1.82/0.63    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.82/0.63    inference(negated_conjecture,[],[f17])).
% 1.82/0.63  % (4086)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.82/0.64  % (4078)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.20/0.65  fof(f17,conjecture,(
% 2.20/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.20/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 2.20/0.65  fof(f527,plain,(
% 2.20/0.65    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_4 | ~spl6_5 | spl6_14)),
% 2.20/0.65    inference(forward_demodulation,[],[f526,f119])).
% 2.20/0.65  fof(f526,plain,(
% 2.20/0.65    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl6_4 | spl6_14)),
% 2.20/0.65    inference(forward_demodulation,[],[f240,f114])).
% 2.20/0.65  fof(f240,plain,(
% 2.20/0.65    sK0 != k1_relset_1(sK0,sK1,sK3) | spl6_14),
% 2.20/0.65    inference(avatar_component_clause,[],[f239])).
% 2.28/0.66  fof(f239,plain,(
% 2.28/0.66    spl6_14 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.28/0.66  fof(f583,plain,(
% 2.28/0.66    k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK3 | (~spl6_4 | ~spl6_11)),
% 2.28/0.66    inference(subsumption_resolution,[],[f577,f518])).
% 2.28/0.66  fof(f518,plain,(
% 2.28/0.66    v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) | ~spl6_4),
% 2.28/0.66    inference(forward_demodulation,[],[f321,f114])).
% 2.28/0.66  fof(f321,plain,(
% 2.28/0.66    v1_funct_2(sK3,k1_relat_1(sK3),sK1)),
% 2.28/0.66    inference(subsumption_resolution,[],[f320,f131])).
% 2.28/0.66  fof(f131,plain,(
% 2.28/0.66    v1_relat_1(sK3)),
% 2.28/0.66    inference(resolution,[],[f53,f75])).
% 2.28/0.66  fof(f75,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f29])).
% 2.28/0.66  fof(f29,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.28/0.66    inference(ennf_transformation,[],[f10])).
% 2.28/0.66  fof(f10,axiom,(
% 2.28/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.28/0.66  fof(f320,plain,(
% 2.28/0.66    v1_funct_2(sK3,k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 2.28/0.66    inference(subsumption_resolution,[],[f316,f51])).
% 2.28/0.66  fof(f51,plain,(
% 2.28/0.66    v1_funct_1(sK3)),
% 2.28/0.66    inference(cnf_transformation,[],[f40])).
% 2.28/0.66  fof(f316,plain,(
% 2.28/0.66    v1_funct_2(sK3,k1_relat_1(sK3),sK1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 2.28/0.66    inference(resolution,[],[f159,f64])).
% 2.28/0.66  fof(f64,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f27])).
% 2.28/0.66  fof(f27,plain,(
% 2.28/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.28/0.66    inference(flattening,[],[f26])).
% 2.28/0.66  fof(f26,plain,(
% 2.28/0.66    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.28/0.66    inference(ennf_transformation,[],[f16])).
% 2.28/0.66  fof(f16,axiom,(
% 2.28/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 2.28/0.66  fof(f159,plain,(
% 2.28/0.66    r1_tarski(k2_relat_1(sK3),sK1)),
% 2.28/0.66    inference(subsumption_resolution,[],[f158,f131])).
% 2.28/0.66  fof(f158,plain,(
% 2.28/0.66    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 2.28/0.66    inference(resolution,[],[f133,f61])).
% 2.28/0.66  fof(f61,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f41])).
% 2.28/0.66  fof(f41,plain,(
% 2.28/0.66    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.28/0.66    inference(nnf_transformation,[],[f25])).
% 2.28/0.66  fof(f25,plain,(
% 2.28/0.66    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.28/0.66    inference(ennf_transformation,[],[f7])).
% 2.28/0.66  fof(f7,axiom,(
% 2.28/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.28/0.66  fof(f133,plain,(
% 2.28/0.66    v5_relat_1(sK3,sK1)),
% 2.28/0.66    inference(resolution,[],[f53,f77])).
% 2.28/0.66  fof(f77,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f31])).
% 2.28/0.66  fof(f31,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.28/0.66    inference(ennf_transformation,[],[f19])).
% 2.28/0.66  fof(f19,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.28/0.66    inference(pure_predicate_removal,[],[f11])).
% 2.28/0.66  fof(f11,axiom,(
% 2.28/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.28/0.66  fof(f577,plain,(
% 2.28/0.66    ~v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK3 | (~spl6_4 | ~spl6_11)),
% 2.28/0.66    inference(resolution,[],[f540,f94])).
% 2.28/0.66  fof(f94,plain,(
% 2.28/0.66    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 2.28/0.66    inference(equality_resolution,[],[f82])).
% 2.28/0.66  fof(f82,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.28/0.66    inference(cnf_transformation,[],[f50])).
% 2.28/0.66  fof(f50,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.28/0.66    inference(nnf_transformation,[],[f33])).
% 2.28/0.66  fof(f33,plain,(
% 2.28/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.28/0.66    inference(flattening,[],[f32])).
% 2.28/0.66  fof(f32,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.28/0.66    inference(ennf_transformation,[],[f13])).
% 2.28/0.66  fof(f13,axiom,(
% 2.28/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.28/0.66  fof(f540,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))) ) | (~spl6_4 | ~spl6_11)),
% 2.28/0.66    inference(subsumption_resolution,[],[f539,f131])).
% 2.28/0.66  fof(f539,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) | ~v1_relat_1(sK3)) ) | (~spl6_4 | ~spl6_11)),
% 2.28/0.66    inference(subsumption_resolution,[],[f538,f51])).
% 2.28/0.66  fof(f538,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | (~spl6_4 | ~spl6_11)),
% 2.28/0.66    inference(subsumption_resolution,[],[f533,f58])).
% 2.28/0.66  fof(f58,plain,(
% 2.28/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f4])).
% 2.28/0.66  fof(f4,axiom,(
% 2.28/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.28/0.66  fof(f533,plain,(
% 2.28/0.66    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | (~spl6_4 | ~spl6_11)),
% 2.28/0.66    inference(superposition,[],[f65,f467])).
% 2.28/0.66  fof(f467,plain,(
% 2.28/0.66    k1_xboole_0 = k2_relat_1(sK3) | (~spl6_4 | ~spl6_11)),
% 2.28/0.66    inference(backward_demodulation,[],[f179,f114])).
% 2.28/0.66  fof(f179,plain,(
% 2.28/0.66    sK1 = k2_relat_1(sK3) | ~spl6_11),
% 2.28/0.66    inference(avatar_component_clause,[],[f177])).
% 2.28/0.66  fof(f177,plain,(
% 2.28/0.66    spl6_11 <=> sK1 = k2_relat_1(sK3)),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.28/0.66  fof(f65,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f27])).
% 2.28/0.66  fof(f483,plain,(
% 2.28/0.66    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_4 | ~spl6_5)),
% 2.28/0.66    inference(backward_demodulation,[],[f435,f114])).
% 2.28/0.66  fof(f435,plain,(
% 2.28/0.66    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl6_5),
% 2.28/0.66    inference(backward_demodulation,[],[f52,f119])).
% 2.28/0.66  fof(f52,plain,(
% 2.28/0.66    v1_funct_2(sK3,sK0,sK1)),
% 2.28/0.66    inference(cnf_transformation,[],[f40])).
% 2.28/0.66  fof(f692,plain,(
% 2.28/0.66    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | spl6_14)),
% 2.28/0.66    inference(forward_demodulation,[],[f621,f636])).
% 2.28/0.66  fof(f636,plain,(
% 2.28/0.66    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_11 | spl6_14)),
% 2.28/0.66    inference(subsumption_resolution,[],[f635,f58])).
% 2.28/0.66  fof(f635,plain,(
% 2.28/0.66    ( ! [X0] : (~r1_tarski(k1_xboole_0,k7_relat_1(k1_xboole_0,X0)) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_11 | spl6_14)),
% 2.28/0.66    inference(forward_demodulation,[],[f589,f584])).
% 2.28/0.66  fof(f589,plain,(
% 2.28/0.66    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~r1_tarski(sK3,k7_relat_1(sK3,X0))) ) | (~spl6_4 | ~spl6_5 | ~spl6_11 | spl6_14)),
% 2.28/0.66    inference(backward_demodulation,[],[f181,f584])).
% 2.28/0.66  fof(f181,plain,(
% 2.28/0.66    ( ! [X0] : (~r1_tarski(sK3,k7_relat_1(sK3,X0)) | sK3 = k7_relat_1(sK3,X0)) )),
% 2.28/0.66    inference(resolution,[],[f157,f68])).
% 2.28/0.66  fof(f68,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f43])).
% 2.28/0.66  fof(f43,plain,(
% 2.28/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.28/0.66    inference(flattening,[],[f42])).
% 2.28/0.66  fof(f42,plain,(
% 2.28/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.28/0.66    inference(nnf_transformation,[],[f3])).
% 2.28/0.66  fof(f3,axiom,(
% 2.28/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.28/0.66  fof(f157,plain,(
% 2.28/0.66    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 2.28/0.66    inference(resolution,[],[f131,f59])).
% 2.28/0.66  fof(f59,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f22])).
% 2.28/0.66  fof(f22,plain,(
% 2.28/0.66    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.28/0.66    inference(ennf_transformation,[],[f8])).
% 2.28/0.66  fof(f8,axiom,(
% 2.28/0.66    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 2.28/0.66  fof(f621,plain,(
% 2.28/0.66    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | spl6_14)),
% 2.28/0.66    inference(backward_demodulation,[],[f513,f584])).
% 2.28/0.66  fof(f513,plain,(
% 2.28/0.66    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7)),
% 2.28/0.66    inference(forward_demodulation,[],[f512,f484])).
% 2.28/0.66  fof(f484,plain,(
% 2.28/0.66    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,X0)) ) | (~spl6_4 | ~spl6_5)),
% 2.28/0.66    inference(backward_demodulation,[],[f438,f114])).
% 2.28/0.66  fof(f438,plain,(
% 2.28/0.66    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(k1_xboole_0,sK1,sK3,X0)) ) | ~spl6_5),
% 2.28/0.66    inference(backward_demodulation,[],[f142,f119])).
% 2.28/0.66  fof(f142,plain,(
% 2.28/0.66    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 2.28/0.66    inference(subsumption_resolution,[],[f136,f51])).
% 2.28/0.66  fof(f136,plain,(
% 2.28/0.66    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) | ~v1_funct_1(sK3)) )),
% 2.28/0.66    inference(resolution,[],[f53,f85])).
% 2.28/0.66  fof(f85,plain,(
% 2.28/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f36])).
% 2.28/0.66  fof(f36,plain,(
% 2.28/0.66    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.28/0.66    inference(flattening,[],[f35])).
% 2.28/0.66  fof(f35,plain,(
% 2.28/0.66    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.28/0.66    inference(ennf_transformation,[],[f15])).
% 2.28/0.66  fof(f15,axiom,(
% 2.28/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.28/0.66  fof(f512,plain,(
% 2.28/0.66    ~v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7)),
% 2.28/0.66    inference(forward_demodulation,[],[f511,f119])).
% 2.28/0.66  fof(f511,plain,(
% 2.28/0.66    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7)),
% 2.28/0.66    inference(forward_demodulation,[],[f510,f437])).
% 2.28/0.66  fof(f437,plain,(
% 2.28/0.66    k1_xboole_0 = sK2 | (~spl6_5 | ~spl6_7)),
% 2.28/0.66    inference(backward_demodulation,[],[f129,f119])).
% 2.28/0.66  fof(f129,plain,(
% 2.28/0.66    sK0 = sK2 | ~spl6_7),
% 2.28/0.66    inference(avatar_component_clause,[],[f127])).
% 2.28/0.66  fof(f127,plain,(
% 2.28/0.66    spl6_7 <=> sK0 = sK2),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.28/0.66  fof(f510,plain,(
% 2.28/0.66    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0) | (spl6_2 | ~spl6_4)),
% 2.28/0.66    inference(forward_demodulation,[],[f106,f114])).
% 2.28/0.66  fof(f106,plain,(
% 2.28/0.66    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl6_2),
% 2.28/0.66    inference(avatar_component_clause,[],[f104])).
% 2.28/0.66  fof(f104,plain,(
% 2.28/0.66    spl6_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.28/0.66  fof(f515,plain,(
% 2.28/0.66    spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_14),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f514])).
% 2.28/0.66  fof(f514,plain,(
% 2.28/0.66    $false | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_14)),
% 2.28/0.66    inference(subsumption_resolution,[],[f513,f478])).
% 2.28/0.66  fof(f478,plain,(
% 2.28/0.66    v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl6_4 | ~spl6_14)),
% 2.28/0.66    inference(backward_demodulation,[],[f378,f114])).
% 2.28/0.66  fof(f378,plain,(
% 2.28/0.66    v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | ~spl6_14),
% 2.28/0.66    inference(superposition,[],[f208,f347])).
% 2.28/0.66  fof(f347,plain,(
% 2.28/0.66    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | ~spl6_14),
% 2.28/0.66    inference(resolution,[],[f315,f58])).
% 2.28/0.66  fof(f315,plain,(
% 2.28/0.66    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl6_14),
% 2.28/0.66    inference(subsumption_resolution,[],[f314,f131])).
% 2.28/0.66  fof(f314,plain,(
% 2.28/0.66    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl6_14),
% 2.28/0.66    inference(superposition,[],[f60,f297])).
% 2.28/0.66  fof(f297,plain,(
% 2.28/0.66    sK0 = k1_relat_1(sK3) | ~spl6_14),
% 2.28/0.66    inference(backward_demodulation,[],[f132,f241])).
% 2.28/0.66  fof(f241,plain,(
% 2.28/0.66    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_14),
% 2.28/0.66    inference(avatar_component_clause,[],[f239])).
% 2.28/0.66  fof(f132,plain,(
% 2.28/0.66    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 2.28/0.66    inference(resolution,[],[f53,f76])).
% 2.28/0.66  fof(f60,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f24])).
% 2.28/0.66  fof(f24,plain,(
% 2.28/0.66    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.28/0.66    inference(flattening,[],[f23])).
% 2.28/0.66  fof(f23,plain,(
% 2.28/0.66    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.28/0.66    inference(ennf_transformation,[],[f9])).
% 2.28/0.66  fof(f9,axiom,(
% 2.28/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 2.28/0.66  fof(f208,plain,(
% 2.28/0.66    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 2.28/0.66    inference(subsumption_resolution,[],[f207,f182])).
% 2.28/0.66  fof(f182,plain,(
% 2.28/0.66    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 2.28/0.66    inference(resolution,[],[f147,f75])).
% 2.28/0.66  fof(f147,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 2.28/0.66    inference(forward_demodulation,[],[f146,f142])).
% 2.28/0.66  fof(f146,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 2.28/0.66    inference(subsumption_resolution,[],[f137,f51])).
% 2.28/0.66  fof(f137,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 2.28/0.66    inference(resolution,[],[f53,f87])).
% 2.28/0.66  fof(f87,plain,(
% 2.28/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f38])).
% 2.28/0.66  fof(f38,plain,(
% 2.28/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.28/0.66    inference(flattening,[],[f37])).
% 2.28/0.66  fof(f37,plain,(
% 2.28/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.28/0.66    inference(ennf_transformation,[],[f14])).
% 2.28/0.66  fof(f14,axiom,(
% 2.28/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 2.28/0.66  fof(f207,plain,(
% 2.28/0.66    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 2.28/0.66    inference(subsumption_resolution,[],[f203,f196])).
% 2.28/0.66  fof(f196,plain,(
% 2.28/0.66    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 2.28/0.66    inference(subsumption_resolution,[],[f195,f51])).
% 2.28/0.66  fof(f195,plain,(
% 2.28/0.66    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_funct_1(sK3)) )),
% 2.28/0.66    inference(subsumption_resolution,[],[f194,f53])).
% 2.28/0.66  fof(f194,plain,(
% 2.28/0.66    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 2.28/0.66    inference(superposition,[],[f86,f142])).
% 2.28/0.66  fof(f86,plain,(
% 2.28/0.66    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f38])).
% 2.28/0.66  fof(f203,plain,(
% 2.28/0.66    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 2.28/0.66    inference(resolution,[],[f202,f64])).
% 2.28/0.66  fof(f202,plain,(
% 2.28/0.66    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 2.28/0.66    inference(subsumption_resolution,[],[f201,f182])).
% 2.28/0.66  fof(f201,plain,(
% 2.28/0.66    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 2.28/0.66    inference(resolution,[],[f184,f61])).
% 2.28/0.66  fof(f184,plain,(
% 2.28/0.66    ( ! [X2] : (v5_relat_1(k7_relat_1(sK3,X2),sK1)) )),
% 2.28/0.66    inference(resolution,[],[f147,f77])).
% 2.28/0.66  fof(f425,plain,(
% 2.28/0.66    ~spl6_10 | spl6_11),
% 2.28/0.66    inference(avatar_split_clause,[],[f319,f177,f173])).
% 2.28/0.66  fof(f173,plain,(
% 2.28/0.66    spl6_10 <=> r1_tarski(sK1,k2_relat_1(sK3))),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.28/0.66  fof(f319,plain,(
% 2.28/0.66    sK1 = k2_relat_1(sK3) | ~r1_tarski(sK1,k2_relat_1(sK3))),
% 2.28/0.66    inference(resolution,[],[f159,f68])).
% 2.28/0.66  fof(f414,plain,(
% 2.28/0.66    ~spl6_6 | spl6_7),
% 2.28/0.66    inference(avatar_split_clause,[],[f301,f127,f123])).
% 2.28/0.66  fof(f123,plain,(
% 2.28/0.66    spl6_6 <=> r1_tarski(sK0,sK2)),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.28/0.66  fof(f301,plain,(
% 2.28/0.66    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 2.28/0.66    inference(resolution,[],[f54,f68])).
% 2.28/0.66  fof(f54,plain,(
% 2.28/0.66    r1_tarski(sK2,sK0)),
% 2.28/0.66    inference(cnf_transformation,[],[f40])).
% 2.28/0.66  fof(f400,plain,(
% 2.28/0.66    spl6_3 | ~spl6_14),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f399])).
% 2.28/0.66  fof(f399,plain,(
% 2.28/0.66    $false | (spl6_3 | ~spl6_14)),
% 2.28/0.66    inference(subsumption_resolution,[],[f393,f145])).
% 2.28/0.66  fof(f145,plain,(
% 2.28/0.66    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 2.28/0.66    inference(backward_demodulation,[],[f110,f142])).
% 2.28/0.66  fof(f110,plain,(
% 2.28/0.66    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 2.28/0.66    inference(avatar_component_clause,[],[f108])).
% 2.28/0.66  fof(f108,plain,(
% 2.28/0.66    spl6_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.28/0.66  fof(f393,plain,(
% 2.28/0.66    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_14),
% 2.28/0.66    inference(superposition,[],[f210,f346])).
% 2.28/0.66  fof(f346,plain,(
% 2.28/0.66    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl6_14),
% 2.28/0.66    inference(resolution,[],[f315,f54])).
% 2.28/0.66  fof(f210,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))) )),
% 2.28/0.66    inference(subsumption_resolution,[],[f209,f182])).
% 2.28/0.66  fof(f209,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) | ~v1_relat_1(k7_relat_1(sK3,X1))) )),
% 2.28/0.66    inference(subsumption_resolution,[],[f204,f196])).
% 2.28/0.66  fof(f204,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) | ~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1))) )),
% 2.28/0.66    inference(resolution,[],[f202,f65])).
% 2.28/0.66  fof(f289,plain,(
% 2.28/0.66    ~spl6_4 | spl6_10),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f288])).
% 2.28/0.66  fof(f288,plain,(
% 2.28/0.66    $false | (~spl6_4 | spl6_10)),
% 2.28/0.66    inference(subsumption_resolution,[],[f272,f58])).
% 2.28/0.66  fof(f272,plain,(
% 2.28/0.66    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | (~spl6_4 | spl6_10)),
% 2.28/0.66    inference(backward_demodulation,[],[f175,f114])).
% 2.28/0.66  fof(f175,plain,(
% 2.28/0.66    ~r1_tarski(sK1,k2_relat_1(sK3)) | spl6_10),
% 2.28/0.66    inference(avatar_component_clause,[],[f173])).
% 2.28/0.66  fof(f286,plain,(
% 2.28/0.66    spl6_3 | ~spl6_4 | ~spl6_5),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f285])).
% 2.28/0.66  fof(f285,plain,(
% 2.28/0.66    $false | (spl6_3 | ~spl6_4 | ~spl6_5)),
% 2.28/0.66    inference(subsumption_resolution,[],[f284,f258])).
% 2.28/0.66  fof(f258,plain,(
% 2.28/0.66    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_5),
% 2.28/0.66    inference(forward_demodulation,[],[f250,f91])).
% 2.28/0.67  fof(f91,plain,(
% 2.28/0.67    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.28/0.67    inference(equality_resolution,[],[f73])).
% 2.28/0.67  fof(f73,plain,(
% 2.28/0.67    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.28/0.67    inference(cnf_transformation,[],[f49])).
% 2.28/0.67  fof(f49,plain,(
% 2.28/0.67    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.28/0.67    inference(flattening,[],[f48])).
% 2.28/0.67  fof(f48,plain,(
% 2.28/0.67    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.28/0.67    inference(nnf_transformation,[],[f5])).
% 2.28/0.67  fof(f5,axiom,(
% 2.28/0.67    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.28/0.67  fof(f250,plain,(
% 2.28/0.67    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))) ) | ~spl6_5),
% 2.28/0.67    inference(backward_demodulation,[],[f147,f119])).
% 2.28/0.67  fof(f284,plain,(
% 2.28/0.67    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | (spl6_3 | ~spl6_4)),
% 2.28/0.67    inference(forward_demodulation,[],[f268,f90])).
% 2.28/0.67  fof(f90,plain,(
% 2.28/0.67    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.28/0.67    inference(equality_resolution,[],[f74])).
% 2.28/0.67  fof(f74,plain,(
% 2.28/0.67    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.28/0.67    inference(cnf_transformation,[],[f49])).
% 2.28/0.67  fof(f268,plain,(
% 2.28/0.67    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (spl6_3 | ~spl6_4)),
% 2.28/0.67    inference(backward_demodulation,[],[f145,f114])).
% 2.28/0.67  fof(f257,plain,(
% 2.28/0.67    ~spl6_5 | spl6_6),
% 2.28/0.67    inference(avatar_contradiction_clause,[],[f256])).
% 2.28/0.67  fof(f256,plain,(
% 2.28/0.67    $false | (~spl6_5 | spl6_6)),
% 2.28/0.67    inference(subsumption_resolution,[],[f246,f58])).
% 2.28/0.67  fof(f246,plain,(
% 2.28/0.67    ~r1_tarski(k1_xboole_0,sK2) | (~spl6_5 | spl6_6)),
% 2.28/0.67    inference(backward_demodulation,[],[f125,f119])).
% 2.28/0.67  fof(f125,plain,(
% 2.28/0.67    ~r1_tarski(sK0,sK2) | spl6_6),
% 2.28/0.67    inference(avatar_component_clause,[],[f123])).
% 2.28/0.67  fof(f242,plain,(
% 2.28/0.67    spl6_14 | spl6_4),
% 2.28/0.67    inference(avatar_split_clause,[],[f139,f113,f239])).
% 2.28/0.67  fof(f139,plain,(
% 2.28/0.67    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.28/0.67    inference(subsumption_resolution,[],[f134,f52])).
% 2.28/0.67  fof(f134,plain,(
% 2.28/0.67    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.28/0.67    inference(resolution,[],[f53,f78])).
% 2.28/0.67  fof(f78,plain,(
% 2.28/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.28/0.67    inference(cnf_transformation,[],[f50])).
% 2.28/0.67  fof(f227,plain,(
% 2.28/0.67    spl6_2 | spl6_4),
% 2.28/0.67    inference(avatar_contradiction_clause,[],[f226])).
% 2.28/0.67  fof(f226,plain,(
% 2.28/0.67    $false | (spl6_2 | spl6_4)),
% 2.28/0.67    inference(subsumption_resolution,[],[f223,f144])).
% 2.28/0.67  fof(f144,plain,(
% 2.28/0.67    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl6_2),
% 2.28/0.67    inference(backward_demodulation,[],[f106,f142])).
% 2.28/0.67  fof(f223,plain,(
% 2.28/0.67    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl6_4),
% 2.28/0.67    inference(superposition,[],[f208,f211])).
% 2.28/0.67  fof(f211,plain,(
% 2.28/0.67    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | spl6_4),
% 2.28/0.67    inference(resolution,[],[f161,f54])).
% 2.28/0.67  fof(f161,plain,(
% 2.28/0.67    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | spl6_4),
% 2.28/0.67    inference(subsumption_resolution,[],[f160,f131])).
% 2.28/0.67  fof(f160,plain,(
% 2.28/0.67    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | spl6_4),
% 2.28/0.67    inference(superposition,[],[f60,f141])).
% 2.28/0.67  fof(f141,plain,(
% 2.28/0.67    sK0 = k1_relat_1(sK3) | spl6_4),
% 2.28/0.67    inference(backward_demodulation,[],[f132,f140])).
% 2.28/0.67  fof(f140,plain,(
% 2.28/0.67    sK0 = k1_relset_1(sK0,sK1,sK3) | spl6_4),
% 2.28/0.67    inference(subsumption_resolution,[],[f139,f115])).
% 2.28/0.67  fof(f115,plain,(
% 2.28/0.67    k1_xboole_0 != sK1 | spl6_4),
% 2.28/0.67    inference(avatar_component_clause,[],[f113])).
% 2.28/0.67  fof(f199,plain,(
% 2.28/0.67    spl6_1),
% 2.28/0.67    inference(avatar_contradiction_clause,[],[f198])).
% 2.28/0.67  fof(f198,plain,(
% 2.28/0.67    $false | spl6_1),
% 2.28/0.67    inference(resolution,[],[f196,f143])).
% 2.28/0.67  fof(f143,plain,(
% 2.28/0.67    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl6_1),
% 2.28/0.67    inference(backward_demodulation,[],[f102,f142])).
% 2.28/0.67  fof(f102,plain,(
% 2.28/0.67    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl6_1),
% 2.28/0.67    inference(avatar_component_clause,[],[f100])).
% 2.28/0.67  fof(f100,plain,(
% 2.28/0.67    spl6_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.28/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.28/0.67  fof(f120,plain,(
% 2.28/0.67    ~spl6_4 | spl6_5),
% 2.28/0.67    inference(avatar_split_clause,[],[f55,f117,f113])).
% 2.28/0.67  fof(f55,plain,(
% 2.28/0.67    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.28/0.67    inference(cnf_transformation,[],[f40])).
% 2.28/0.67  fof(f111,plain,(
% 2.28/0.67    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 2.28/0.67    inference(avatar_split_clause,[],[f56,f108,f104,f100])).
% 2.28/0.67  fof(f56,plain,(
% 2.28/0.67    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.28/0.67    inference(cnf_transformation,[],[f40])).
% 2.28/0.67  % SZS output end Proof for theBenchmark
% 2.28/0.67  % (4067)------------------------------
% 2.28/0.67  % (4067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.67  % (4067)Termination reason: Refutation
% 2.28/0.67  
% 2.28/0.67  % (4067)Memory used [KB]: 11001
% 2.28/0.67  % (4067)Time elapsed: 0.227 s
% 2.28/0.67  % (4067)------------------------------
% 2.28/0.67  % (4067)------------------------------
% 2.28/0.67  % (4058)Success in time 0.315 s
%------------------------------------------------------------------------------
