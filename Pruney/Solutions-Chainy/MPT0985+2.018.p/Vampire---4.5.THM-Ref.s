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
% DateTime   : Thu Dec  3 13:02:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  124 (1276 expanded)
%              Number of leaves         :   19 ( 307 expanded)
%              Depth                    :   31
%              Number of atoms          :  400 (7326 expanded)
%              Number of equality atoms :  107 (1171 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(subsumption_resolution,[],[f310,f106])).

fof(f106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f82,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f310,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f308,f266])).

fof(f266,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f54,f264])).

fof(f264,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f252,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f81,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f252,plain,(
    v1_xboole_0(sK3) ),
    inference(resolution,[],[f243,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f112,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f71,f60])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f243,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f227,f93])).

fof(f227,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f56,f225])).

fof(f225,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f224,f107])).

fof(f107,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f82,f56])).

fof(f224,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f222,f54])).

fof(f222,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f221,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f221,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f220,f105])).

fof(f105,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f77,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f220,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f219,f186])).

fof(f186,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f183,f155])).

fof(f155,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f84,f56])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f183,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f181,f55])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f181,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f85,f116])).

fof(f116,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f89,f56])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f38,f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
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
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f219,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f204,f218])).

fof(f218,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(forward_demodulation,[],[f217,f147])).

fof(f147,plain,(
    sK2 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f128,f145])).

fof(f145,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f141,f58])).

fof(f58,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f141,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f83,f56])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f128,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f127,f107])).

fof(f127,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f126,f54])).

fof(f126,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f217,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),X0))) ) ),
    inference(subsumption_resolution,[],[f216,f107])).

fof(f216,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),X0)))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f215,f54])).

fof(f215,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),X0)))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f173,f131])).

fof(f131,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f130,f107])).

fof(f130,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f129,f54])).

fof(f129,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f70,f57])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f173,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(X3)),X4)
      | m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X3)),X4)))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f169,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f169,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(X3)),X4)
      | m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X3)),X4)))
      | ~ v1_relat_1(k2_funct_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f74,f68])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f204,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f203,f82])).

fof(f203,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f146,f59])).

fof(f59,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f146,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(sK3),sK2,X1)
      | ~ r1_tarski(k1_relat_1(sK3),X1)
      | ~ v1_funct_1(k2_funct_1(sK3))
      | ~ v1_relat_1(k2_funct_1(sK3)) ) ),
    inference(backward_demodulation,[],[f139,f145])).

fof(f139,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK3),X1)
      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X1)
      | ~ v1_funct_1(k2_funct_1(sK3))
      | ~ v1_relat_1(k2_funct_1(sK3)) ) ),
    inference(forward_demodulation,[],[f135,f131])).

fof(f135,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X1)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X1)
      | ~ v1_funct_1(k2_funct_1(sK3))
      | ~ v1_relat_1(k2_funct_1(sK3)) ) ),
    inference(superposition,[],[f73,f128])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f308,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f291,f68])).

fof(f291,plain,(
    ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f290,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f290,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f289,f61])).

fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f289,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK1)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f270,f264])).

fof(f270,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(backward_demodulation,[],[f219,f264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:04:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (21534)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (21554)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (21535)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (21551)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (21543)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (21535)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (21555)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (21528)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (21539)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (21530)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (21532)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (21546)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.55  % (21531)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.43/0.55  % (21556)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.55  % (21540)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.56  % (21533)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.43/0.56  % (21550)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.56  % (21544)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.56  % (21549)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.56  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f311,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(subsumption_resolution,[],[f310,f106])).
% 1.43/0.56  fof(f106,plain,(
% 1.43/0.56    v1_relat_1(k1_xboole_0)),
% 1.43/0.56    inference(resolution,[],[f82,f64])).
% 1.43/0.56  fof(f64,plain,(
% 1.43/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f6])).
% 1.43/0.56  fof(f6,axiom,(
% 1.43/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.43/0.56  fof(f82,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f34])).
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f13])).
% 1.43/0.56  fof(f13,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.43/0.56  fof(f310,plain,(
% 1.43/0.56    ~v1_relat_1(k1_xboole_0)),
% 1.43/0.56    inference(subsumption_resolution,[],[f308,f266])).
% 1.43/0.56  fof(f266,plain,(
% 1.43/0.56    v1_funct_1(k1_xboole_0)),
% 1.43/0.56    inference(backward_demodulation,[],[f54,f264])).
% 1.43/0.56  fof(f264,plain,(
% 1.43/0.56    k1_xboole_0 = sK3),
% 1.43/0.56    inference(resolution,[],[f252,f102])).
% 1.43/0.56  fof(f102,plain,(
% 1.43/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.43/0.56    inference(resolution,[],[f81,f60])).
% 1.43/0.56  fof(f60,plain,(
% 1.43/0.56    v1_xboole_0(k1_xboole_0)),
% 1.43/0.56    inference(cnf_transformation,[],[f2])).
% 1.43/0.56  fof(f2,axiom,(
% 1.43/0.56    v1_xboole_0(k1_xboole_0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.43/0.56  fof(f81,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f33])).
% 1.43/0.56  fof(f33,plain,(
% 1.43/0.56    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f4])).
% 1.43/0.56  fof(f4,axiom,(
% 1.43/0.56    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.43/0.56  fof(f252,plain,(
% 1.43/0.56    v1_xboole_0(sK3)),
% 1.43/0.56    inference(resolution,[],[f243,f113])).
% 1.43/0.56  fof(f113,plain,(
% 1.43/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f112,f93])).
% 1.43/0.56  fof(f93,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.43/0.56    inference(equality_resolution,[],[f80])).
% 1.43/0.56  fof(f80,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.43/0.56    inference(cnf_transformation,[],[f50])).
% 1.43/0.56  fof(f50,plain,(
% 1.43/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.43/0.56    inference(flattening,[],[f49])).
% 1.43/0.56  fof(f49,plain,(
% 1.43/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.43/0.56    inference(nnf_transformation,[],[f5])).
% 1.43/0.56  fof(f5,axiom,(
% 1.43/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.43/0.56  fof(f112,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 1.43/0.56    inference(resolution,[],[f71,f60])).
% 1.43/0.56  fof(f71,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f29])).
% 1.43/0.56  fof(f29,plain,(
% 1.43/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f14])).
% 1.43/0.56  fof(f14,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.43/0.56  fof(f243,plain,(
% 1.43/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.43/0.56    inference(forward_demodulation,[],[f227,f93])).
% 1.43/0.56  fof(f227,plain,(
% 1.43/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.43/0.56    inference(backward_demodulation,[],[f56,f225])).
% 1.43/0.56  fof(f225,plain,(
% 1.43/0.56    k1_xboole_0 = sK2),
% 1.43/0.56    inference(subsumption_resolution,[],[f224,f107])).
% 1.43/0.56  fof(f107,plain,(
% 1.43/0.56    v1_relat_1(sK3)),
% 1.43/0.56    inference(resolution,[],[f82,f56])).
% 1.43/0.56  fof(f224,plain,(
% 1.43/0.56    k1_xboole_0 = sK2 | ~v1_relat_1(sK3)),
% 1.43/0.56    inference(subsumption_resolution,[],[f222,f54])).
% 1.43/0.56  fof(f222,plain,(
% 1.43/0.56    k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.43/0.56    inference(resolution,[],[f221,f68])).
% 1.43/0.56  fof(f68,plain,(
% 1.43/0.56    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f26])).
% 1.43/0.56  fof(f26,plain,(
% 1.43/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(flattening,[],[f25])).
% 1.43/0.56  fof(f25,plain,(
% 1.43/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f11])).
% 1.43/0.56  fof(f11,axiom,(
% 1.43/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.43/0.56  fof(f221,plain,(
% 1.43/0.56    ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 1.43/0.56    inference(subsumption_resolution,[],[f220,f105])).
% 1.43/0.56  fof(f105,plain,(
% 1.43/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f104])).
% 1.43/0.56  fof(f104,plain,(
% 1.43/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.43/0.56    inference(resolution,[],[f77,f76])).
% 1.43/0.56  fof(f76,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f48])).
% 1.43/0.56  fof(f48,plain,(
% 1.43/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 1.43/0.56  fof(f47,plain,(
% 1.43/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f46,plain,(
% 1.43/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.56    inference(rectify,[],[f45])).
% 1.43/0.56  fof(f45,plain,(
% 1.43/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.56    inference(nnf_transformation,[],[f32])).
% 1.43/0.56  fof(f32,plain,(
% 1.43/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f1])).
% 1.43/0.56  fof(f1,axiom,(
% 1.43/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.43/0.56  fof(f77,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f48])).
% 1.43/0.56  fof(f220,plain,(
% 1.43/0.56    ~r1_tarski(sK1,sK1) | ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 1.43/0.56    inference(superposition,[],[f219,f186])).
% 1.43/0.56  fof(f186,plain,(
% 1.43/0.56    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.43/0.56    inference(superposition,[],[f183,f155])).
% 1.43/0.56  fof(f155,plain,(
% 1.43/0.56    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.43/0.56    inference(resolution,[],[f84,f56])).
% 1.43/0.56  fof(f84,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f36])).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f15])).
% 1.43/0.56  fof(f15,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.43/0.56  fof(f183,plain,(
% 1.43/0.56    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 1.43/0.56    inference(subsumption_resolution,[],[f181,f55])).
% 1.43/0.56  fof(f55,plain,(
% 1.43/0.56    v1_funct_2(sK3,sK1,sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f44,plain,(
% 1.43/0.56    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f43])).
% 1.43/0.56  fof(f43,plain,(
% 1.43/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f22,plain,(
% 1.43/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.43/0.56    inference(flattening,[],[f21])).
% 1.43/0.56  fof(f21,plain,(
% 1.43/0.56    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.43/0.56    inference(ennf_transformation,[],[f20])).
% 1.43/0.56  fof(f20,negated_conjecture,(
% 1.43/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.43/0.56    inference(negated_conjecture,[],[f19])).
% 1.43/0.56  fof(f19,conjecture,(
% 1.43/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.43/0.56  fof(f181,plain,(
% 1.43/0.56    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.43/0.56    inference(resolution,[],[f85,f116])).
% 1.43/0.56  fof(f116,plain,(
% 1.43/0.56    sP0(sK1,sK3,sK2)),
% 1.43/0.56    inference(resolution,[],[f89,f56])).
% 1.43/0.56  fof(f89,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f53])).
% 1.43/0.56  fof(f53,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(nnf_transformation,[],[f42])).
% 1.43/0.56  fof(f42,plain,(
% 1.43/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(definition_folding,[],[f38,f41])).
% 1.43/0.56  fof(f41,plain,(
% 1.43/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.43/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.43/0.56  fof(f38,plain,(
% 1.43/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(flattening,[],[f37])).
% 1.43/0.56  fof(f37,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f17])).
% 1.43/0.56  fof(f17,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.43/0.56  fof(f85,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f52])).
% 1.43/0.56  fof(f52,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.43/0.56    inference(rectify,[],[f51])).
% 1.43/0.56  fof(f51,plain,(
% 1.43/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.43/0.56    inference(nnf_transformation,[],[f41])).
% 1.43/0.56  fof(f219,plain,(
% 1.43/0.56    ~r1_tarski(k1_relat_1(sK3),sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.43/0.56    inference(subsumption_resolution,[],[f204,f218])).
% 1.43/0.56  fof(f218,plain,(
% 1.43/0.56    ( ! [X0] : (m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~r1_tarski(k1_relat_1(sK3),X0)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f217,f147])).
% 1.43/0.56  fof(f147,plain,(
% 1.43/0.56    sK2 = k1_relat_1(k2_funct_1(sK3))),
% 1.43/0.56    inference(backward_demodulation,[],[f128,f145])).
% 1.43/0.56  fof(f145,plain,(
% 1.43/0.56    sK2 = k2_relat_1(sK3)),
% 1.43/0.56    inference(forward_demodulation,[],[f141,f58])).
% 1.43/0.56  fof(f58,plain,(
% 1.43/0.56    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f141,plain,(
% 1.43/0.56    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.43/0.56    inference(resolution,[],[f83,f56])).
% 1.43/0.56  fof(f83,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f35])).
% 1.43/0.56  fof(f35,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f16])).
% 1.43/0.56  fof(f16,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.43/0.56  fof(f128,plain,(
% 1.43/0.56    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.43/0.56    inference(subsumption_resolution,[],[f127,f107])).
% 1.43/0.56  fof(f127,plain,(
% 1.43/0.56    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.43/0.56    inference(subsumption_resolution,[],[f126,f54])).
% 1.43/0.56  fof(f126,plain,(
% 1.43/0.56    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.43/0.56    inference(resolution,[],[f69,f57])).
% 1.43/0.56  fof(f57,plain,(
% 1.43/0.56    v2_funct_1(sK3)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f69,plain,(
% 1.43/0.56    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f28])).
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(flattening,[],[f27])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f12])).
% 1.43/0.56  fof(f12,axiom,(
% 1.43/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.43/0.56  fof(f217,plain,(
% 1.43/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),X0)))) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f216,f107])).
% 1.43/0.56  fof(f216,plain,(
% 1.43/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),X0))) | ~v1_relat_1(sK3)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f215,f54])).
% 1.43/0.56  fof(f215,plain,(
% 1.43/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),X0))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.43/0.56    inference(superposition,[],[f173,f131])).
% 1.43/0.56  fof(f131,plain,(
% 1.43/0.56    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 1.43/0.56    inference(subsumption_resolution,[],[f130,f107])).
% 1.43/0.56  fof(f130,plain,(
% 1.43/0.56    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.43/0.56    inference(subsumption_resolution,[],[f129,f54])).
% 1.43/0.56  fof(f129,plain,(
% 1.43/0.56    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.43/0.56    inference(resolution,[],[f70,f57])).
% 1.43/0.56  fof(f70,plain,(
% 1.43/0.56    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f28])).
% 1.43/0.56  fof(f173,plain,(
% 1.43/0.56    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(k2_funct_1(X3)),X4) | m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X3)),X4))) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f169,f67])).
% 1.43/0.56  fof(f67,plain,(
% 1.43/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f26])).
% 1.43/0.56  fof(f169,plain,(
% 1.43/0.56    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(k2_funct_1(X3)),X4) | m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X3)),X4))) | ~v1_relat_1(k2_funct_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.43/0.56    inference(resolution,[],[f74,f68])).
% 1.43/0.56  fof(f74,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f31])).
% 1.43/0.56  fof(f31,plain,(
% 1.43/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f30])).
% 1.43/0.56  fof(f30,plain,(
% 1.43/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.43/0.56    inference(ennf_transformation,[],[f18])).
% 1.43/0.56  fof(f18,axiom,(
% 1.43/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.43/0.56  fof(f204,plain,(
% 1.43/0.56    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3)) | ~r1_tarski(k1_relat_1(sK3),sK1)),
% 1.43/0.56    inference(subsumption_resolution,[],[f203,f82])).
% 1.43/0.56  fof(f203,plain,(
% 1.43/0.56    ~r1_tarski(k1_relat_1(sK3),sK1) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f202])).
% 1.43/0.56  fof(f202,plain,(
% 1.43/0.56    ~r1_tarski(k1_relat_1(sK3),sK1) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.43/0.56    inference(resolution,[],[f146,f59])).
% 1.43/0.56  fof(f59,plain,(
% 1.43/0.56    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f146,plain,(
% 1.43/0.56    ( ! [X1] : (v1_funct_2(k2_funct_1(sK3),sK2,X1) | ~r1_tarski(k1_relat_1(sK3),X1) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) )),
% 1.43/0.56    inference(backward_demodulation,[],[f139,f145])).
% 1.43/0.56  fof(f139,plain,(
% 1.43/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(sK3),X1) | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X1) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) )),
% 1.43/0.56    inference(forward_demodulation,[],[f135,f131])).
% 1.43/0.56  fof(f135,plain,(
% 1.43/0.56    ( ! [X1] : (v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X1) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X1) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))) )),
% 1.43/0.56    inference(superposition,[],[f73,f128])).
% 1.43/0.56  fof(f73,plain,(
% 1.43/0.56    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f31])).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f54,plain,(
% 1.43/0.56    v1_funct_1(sK3)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f308,plain,(
% 1.43/0.56    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.43/0.56    inference(resolution,[],[f291,f68])).
% 1.43/0.56  fof(f291,plain,(
% 1.43/0.56    ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 1.43/0.56    inference(subsumption_resolution,[],[f290,f63])).
% 1.43/0.56  fof(f63,plain,(
% 1.43/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f3])).
% 1.43/0.56  fof(f3,axiom,(
% 1.43/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.43/0.56  fof(f290,plain,(
% 1.43/0.56    ~r1_tarski(k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 1.43/0.56    inference(forward_demodulation,[],[f289,f61])).
% 1.43/0.56  fof(f61,plain,(
% 1.43/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.43/0.56    inference(cnf_transformation,[],[f9])).
% 1.43/0.56  fof(f9,axiom,(
% 1.43/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.43/0.56  fof(f289,plain,(
% 1.43/0.56    ~r1_tarski(k1_relat_1(k1_xboole_0),sK1) | ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 1.43/0.56    inference(forward_demodulation,[],[f270,f264])).
% 1.43/0.56  fof(f270,plain,(
% 1.43/0.56    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(sK3),sK1)),
% 1.43/0.56    inference(backward_demodulation,[],[f219,f264])).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (21535)------------------------------
% 1.43/0.56  % (21535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (21535)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (21535)Memory used [KB]: 6396
% 1.43/0.56  % (21535)Time elapsed: 0.108 s
% 1.43/0.56  % (21535)------------------------------
% 1.43/0.56  % (21535)------------------------------
% 1.43/0.56  % (21527)Success in time 0.192 s
%------------------------------------------------------------------------------
