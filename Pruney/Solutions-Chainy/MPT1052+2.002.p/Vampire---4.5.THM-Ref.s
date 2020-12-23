%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:03 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  116 (3288 expanded)
%              Number of leaves         :   17 ( 717 expanded)
%              Depth                    :   32
%              Number of atoms          :  322 (12279 expanded)
%              Number of equality atoms :  137 (3618 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f845,plain,(
    $false ),
    inference(subsumption_resolution,[],[f844,f54])).

% (13874)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (13868)Refutation not found, incomplete strategy% (13868)------------------------------
% (13868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13879)Termination reason: Refutation not found, incomplete strategy

% (13879)Memory used [KB]: 10874
% (13879)Time elapsed: 0.151 s
% (13879)------------------------------
% (13879)------------------------------
% (13880)Termination reason: Refutation not found, incomplete strategy

% (13880)Memory used [KB]: 1791
% (13880)Time elapsed: 0.149 s
% (13880)------------------------------
% (13880)------------------------------
% (13868)Termination reason: Refutation not found, incomplete strategy

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

% (13868)Memory used [KB]: 10618
% (13868)Time elapsed: 0.150 s
% (13868)------------------------------
% (13868)------------------------------
fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f844,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f843,f831])).

fof(f831,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f810])).

fof(f810,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f90,f809])).

fof(f809,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f808,f406])).

fof(f406,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f300,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f300,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f97,f296])).

fof(f296,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f295,f216])).

fof(f216,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f206,f132])).

fof(f132,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f131,f97])).

fof(f131,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f128,f96])).

fof(f96,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f52,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
      | sK0 != k1_relat_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
        | sK0 != k1_relat_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

fof(f128,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f106,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
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
    inference(nnf_transformation,[],[f38])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f106,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f97,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f206,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f205,f51])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f205,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f204,f54])).

fof(f204,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f161,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f161,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( sK0 != sK0
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f53,f132])).

fof(f53,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f295,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f293,f203])).

fof(f203,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f161,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f293,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f140,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f140,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(k2_zfmisc_1(sK0,sK1)))) ),
    inference(resolution,[],[f116,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f116,plain,(
    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f115,f51])).

fof(f115,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f112,f67])).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f112,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f109,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f109,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f97,f74])).

fof(f97,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f52,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f808,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f807,f83])).

fof(f807,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f792,f435])).

fof(f435,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f308,f427])).

fof(f427,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f331,f73])).

fof(f73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f331,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f158,f296])).

fof(f158,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f117,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f117,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f105,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f105,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK3(sK1),sK1) ),
    inference(resolution,[],[f101,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f98,plain,(
    ~ v1_xboole_0(k1_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f52,f62])).

fof(f308,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f106,f296])).

fof(f792,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f431,f89])).

fof(f89,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f431,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f299,f427])).

fof(f299,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f96,f296])).

fof(f90,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(resolution,[],[f51,f59])).

fof(f843,plain,(
    ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f834])).

fof(f834,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f456,f831])).

fof(f456,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f333,f427])).

fof(f333,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | k1_xboole_0 != sK0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f162,f296])).

fof(f162,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f160,f51])).

fof(f160,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f53,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.50  % (13858)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (13861)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (13866)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (13866)Refutation not found, incomplete strategy% (13866)------------------------------
% 0.20/0.51  % (13866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13862)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (13884)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (13865)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (13881)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (13875)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (13866)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13866)Memory used [KB]: 10874
% 0.20/0.52  % (13866)Time elapsed: 0.093 s
% 0.20/0.52  % (13866)------------------------------
% 0.20/0.52  % (13866)------------------------------
% 0.20/0.52  % (13873)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (13863)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (13869)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (13859)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (13882)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (13870)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (13864)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (13860)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (13860)Refutation not found, incomplete strategy% (13860)------------------------------
% 0.20/0.54  % (13860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13860)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13860)Memory used [KB]: 10874
% 0.20/0.54  % (13860)Time elapsed: 0.126 s
% 0.20/0.54  % (13860)------------------------------
% 0.20/0.54  % (13860)------------------------------
% 0.20/0.54  % (13888)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (13876)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (13887)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (13885)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (13886)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (13880)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (13877)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (13867)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (13878)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (13868)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (13879)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (13871)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (13879)Refutation not found, incomplete strategy% (13879)------------------------------
% 0.20/0.55  % (13879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13883)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.55  % (13880)Refutation not found, incomplete strategy% (13880)------------------------------
% 1.51/0.55  % (13880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (13858)Refutation found. Thanks to Tanya!
% 1.51/0.55  % SZS status Theorem for theBenchmark
% 1.51/0.55  % SZS output start Proof for theBenchmark
% 1.51/0.55  fof(f845,plain,(
% 1.51/0.55    $false),
% 1.51/0.55    inference(subsumption_resolution,[],[f844,f54])).
% 1.51/0.56  % (13874)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.56  % (13868)Refutation not found, incomplete strategy% (13868)------------------------------
% 1.51/0.56  % (13868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (13879)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (13879)Memory used [KB]: 10874
% 1.51/0.56  % (13879)Time elapsed: 0.151 s
% 1.51/0.56  % (13879)------------------------------
% 1.51/0.56  % (13879)------------------------------
% 1.51/0.56  % (13880)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (13880)Memory used [KB]: 1791
% 1.51/0.56  % (13880)Time elapsed: 0.149 s
% 1.51/0.56  % (13880)------------------------------
% 1.51/0.56  % (13880)------------------------------
% 1.51/0.56  % (13868)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  fof(f54,plain,(
% 1.51/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f6])).
% 1.51/0.57  % (13868)Memory used [KB]: 10618
% 1.51/0.57  % (13868)Time elapsed: 0.150 s
% 1.51/0.57  % (13868)------------------------------
% 1.51/0.57  % (13868)------------------------------
% 1.51/0.57  fof(f6,axiom,(
% 1.51/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.51/0.57  fof(f844,plain,(
% 1.51/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.51/0.57    inference(forward_demodulation,[],[f843,f831])).
% 1.51/0.57  fof(f831,plain,(
% 1.51/0.57    k1_xboole_0 = k2_relat_1(sK2)),
% 1.51/0.57    inference(trivial_inequality_removal,[],[f810])).
% 1.51/0.57  fof(f810,plain,(
% 1.51/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2)),
% 1.51/0.57    inference(backward_demodulation,[],[f90,f809])).
% 1.51/0.57  fof(f809,plain,(
% 1.51/0.57    k1_xboole_0 = k1_relat_1(sK2)),
% 1.51/0.57    inference(subsumption_resolution,[],[f808,f406])).
% 1.51/0.57  fof(f406,plain,(
% 1.51/0.57    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.51/0.57    inference(forward_demodulation,[],[f300,f83])).
% 1.51/0.57  fof(f83,plain,(
% 1.51/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.51/0.57    inference(equality_resolution,[],[f71])).
% 1.51/0.57  fof(f71,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f48])).
% 1.51/0.57  fof(f48,plain,(
% 1.51/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.51/0.57    inference(flattening,[],[f47])).
% 1.51/0.57  fof(f47,plain,(
% 1.51/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.51/0.57    inference(nnf_transformation,[],[f8])).
% 1.51/0.57  fof(f8,axiom,(
% 1.51/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.51/0.57  fof(f300,plain,(
% 1.51/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.51/0.57    inference(backward_demodulation,[],[f97,f296])).
% 1.51/0.57  fof(f296,plain,(
% 1.51/0.57    k1_xboole_0 = sK1),
% 1.51/0.57    inference(subsumption_resolution,[],[f295,f216])).
% 1.51/0.57  fof(f216,plain,(
% 1.51/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.51/0.57    inference(duplicate_literal_removal,[],[f213])).
% 1.51/0.57  fof(f213,plain,(
% 1.51/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.51/0.57    inference(superposition,[],[f206,f132])).
% 1.62/0.57  fof(f132,plain,(
% 1.62/0.57    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.62/0.57    inference(subsumption_resolution,[],[f131,f97])).
% 1.62/0.57  fof(f131,plain,(
% 1.62/0.57    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(subsumption_resolution,[],[f128,f96])).
% 1.62/0.57  fof(f96,plain,(
% 1.62/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.62/0.57    inference(resolution,[],[f52,f65])).
% 1.62/0.57  fof(f65,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f34])).
% 1.62/0.57  fof(f34,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.62/0.57    inference(ennf_transformation,[],[f23])).
% 1.62/0.57  fof(f23,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 1.62/0.57    inference(pure_predicate_removal,[],[f19])).
% 1.62/0.57  fof(f19,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 1.62/0.57  fof(f52,plain,(
% 1.62/0.57    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.62/0.57    inference(cnf_transformation,[],[f41])).
% 1.62/0.57  fof(f41,plain,(
% 1.62/0.57    (~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)) & v1_relat_1(sK2)),
% 1.62/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f40])).
% 1.62/0.57  fof(f40,plain,(
% 1.62/0.57    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)) & v1_relat_1(sK2))),
% 1.62/0.57    introduced(choice_axiom,[])).
% 1.62/0.57  fof(f26,plain,(
% 1.62/0.57    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 1.62/0.57    inference(flattening,[],[f25])).
% 1.62/0.57  fof(f25,plain,(
% 1.62/0.57    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 1.62/0.57    inference(ennf_transformation,[],[f24])).
% 1.62/0.57  fof(f24,plain,(
% 1.62/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.62/0.57    inference(pure_predicate_removal,[],[f22])).
% 1.62/0.57  fof(f22,negated_conjecture,(
% 1.62/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.62/0.57    inference(negated_conjecture,[],[f21])).
% 1.62/0.57  fof(f21,conjecture,(
% 1.62/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).
% 1.62/0.57  fof(f128,plain,(
% 1.62/0.57    sK0 = k1_relat_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(superposition,[],[f106,f76])).
% 1.62/0.57  fof(f76,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f50])).
% 1.62/0.57  fof(f50,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(nnf_transformation,[],[f38])).
% 1.62/0.57  fof(f38,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(flattening,[],[f37])).
% 1.62/0.57  fof(f37,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(ennf_transformation,[],[f17])).
% 1.62/0.57  fof(f17,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.62/0.57  fof(f106,plain,(
% 1.62/0.57    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.62/0.57    inference(resolution,[],[f97,f82])).
% 1.62/0.57  fof(f82,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f39])).
% 1.62/0.57  fof(f39,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(ennf_transformation,[],[f16])).
% 1.62/0.57  fof(f16,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.62/0.57  fof(f206,plain,(
% 1.62/0.57    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.62/0.57    inference(subsumption_resolution,[],[f205,f51])).
% 1.62/0.57  fof(f51,plain,(
% 1.62/0.57    v1_relat_1(sK2)),
% 1.62/0.57    inference(cnf_transformation,[],[f41])).
% 1.62/0.57  fof(f205,plain,(
% 1.62/0.57    k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.57    inference(subsumption_resolution,[],[f204,f54])).
% 1.62/0.57  fof(f204,plain,(
% 1.62/0.57    ~r1_tarski(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.57    inference(superposition,[],[f161,f59])).
% 1.62/0.57  fof(f59,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f42])).
% 1.62/0.57  fof(f42,plain,(
% 1.62/0.57    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(nnf_transformation,[],[f30])).
% 1.62/0.57  fof(f30,plain,(
% 1.62/0.57    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(ennf_transformation,[],[f15])).
% 1.62/0.57  fof(f15,axiom,(
% 1.62/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.62/0.57  fof(f161,plain,(
% 1.62/0.57    ~r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1),
% 1.62/0.57    inference(trivial_inequality_removal,[],[f159])).
% 1.62/0.57  fof(f159,plain,(
% 1.62/0.57    sK0 != sK0 | ~r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1),
% 1.62/0.57    inference(superposition,[],[f53,f132])).
% 1.62/0.57  fof(f53,plain,(
% 1.62/0.57    sK0 != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1)),
% 1.62/0.57    inference(cnf_transformation,[],[f41])).
% 1.62/0.57  fof(f295,plain,(
% 1.62/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.62/0.57    inference(subsumption_resolution,[],[f293,f203])).
% 1.62/0.57  fof(f203,plain,(
% 1.62/0.57    k1_xboole_0 = sK1 | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.62/0.57    inference(resolution,[],[f161,f74])).
% 1.62/0.57  fof(f74,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f49])).
% 1.62/0.57  fof(f49,plain,(
% 1.62/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.62/0.57    inference(nnf_transformation,[],[f9])).
% 1.62/0.57  fof(f9,axiom,(
% 1.62/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.62/0.57  fof(f293,plain,(
% 1.62/0.57    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.62/0.57    inference(superposition,[],[f140,f56])).
% 1.62/0.57  fof(f56,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f27,plain,(
% 1.62/0.57    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.62/0.57    inference(ennf_transformation,[],[f13])).
% 1.62/0.57  fof(f13,axiom,(
% 1.62/0.57    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 1.62/0.57  fof(f140,plain,(
% 1.62/0.57    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k2_relat_1(k2_zfmisc_1(sK0,sK1))))),
% 1.62/0.57    inference(resolution,[],[f116,f75])).
% 1.62/0.57  fof(f75,plain,(
% 1.62/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f49])).
% 1.62/0.57  fof(f116,plain,(
% 1.62/0.57    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(subsumption_resolution,[],[f115,f51])).
% 1.62/0.57  fof(f115,plain,(
% 1.62/0.57    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~v1_relat_1(sK2)),
% 1.62/0.57    inference(subsumption_resolution,[],[f112,f67])).
% 1.62/0.57  fof(f67,plain,(
% 1.62/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f12])).
% 1.62/0.57  fof(f12,axiom,(
% 1.62/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.62/0.57  fof(f112,plain,(
% 1.62/0.57    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~v1_relat_1(sK2)),
% 1.62/0.57    inference(resolution,[],[f109,f58])).
% 1.62/0.57  fof(f58,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f29])).
% 1.62/0.57  fof(f29,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(flattening,[],[f28])).
% 1.62/0.57  fof(f28,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(ennf_transformation,[],[f14])).
% 1.62/0.57  fof(f14,axiom,(
% 1.62/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.62/0.57  fof(f109,plain,(
% 1.62/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.62/0.57    inference(resolution,[],[f97,f74])).
% 1.62/0.57  fof(f97,plain,(
% 1.62/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(resolution,[],[f52,f66])).
% 1.62/0.57  fof(f66,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f34])).
% 1.62/0.57  fof(f808,plain,(
% 1.62/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.62/0.57    inference(forward_demodulation,[],[f807,f83])).
% 1.62/0.57  fof(f807,plain,(
% 1.62/0.57    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.62/0.57    inference(forward_demodulation,[],[f792,f435])).
% 1.62/0.57  fof(f435,plain,(
% 1.62/0.57    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 1.62/0.57    inference(backward_demodulation,[],[f308,f427])).
% 1.62/0.57  fof(f427,plain,(
% 1.62/0.57    k1_xboole_0 = sK0),
% 1.62/0.57    inference(subsumption_resolution,[],[f331,f73])).
% 1.62/0.57  fof(f73,plain,(
% 1.62/0.57    v1_xboole_0(k1_xboole_0)),
% 1.62/0.57    inference(cnf_transformation,[],[f2])).
% 1.62/0.57  fof(f2,axiom,(
% 1.62/0.57    v1_xboole_0(k1_xboole_0)),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.62/0.57  fof(f331,plain,(
% 1.62/0.57    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0),
% 1.62/0.57    inference(backward_demodulation,[],[f158,f296])).
% 1.62/0.57  fof(f158,plain,(
% 1.62/0.57    ~v1_xboole_0(sK1) | k1_xboole_0 = sK0),
% 1.62/0.57    inference(resolution,[],[f117,f62])).
% 1.62/0.57  fof(f62,plain,(
% 1.62/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f46])).
% 1.62/0.57  fof(f46,plain,(
% 1.62/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.62/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 1.62/0.57  fof(f45,plain,(
% 1.62/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.62/0.57    introduced(choice_axiom,[])).
% 1.62/0.57  fof(f44,plain,(
% 1.62/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.62/0.57    inference(rectify,[],[f43])).
% 1.62/0.57  fof(f43,plain,(
% 1.62/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.62/0.57    inference(nnf_transformation,[],[f1])).
% 1.62/0.57  fof(f1,axiom,(
% 1.62/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.62/0.57  fof(f117,plain,(
% 1.62/0.57    r2_hidden(sK3(sK1),sK1) | k1_xboole_0 = sK0),
% 1.62/0.57    inference(resolution,[],[f105,f72])).
% 1.62/0.57  fof(f72,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f36])).
% 1.62/0.57  fof(f36,plain,(
% 1.62/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.62/0.57    inference(ennf_transformation,[],[f3])).
% 1.62/0.57  fof(f3,axiom,(
% 1.62/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.62/0.57  fof(f105,plain,(
% 1.62/0.57    v1_xboole_0(sK0) | r2_hidden(sK3(sK1),sK1)),
% 1.62/0.57    inference(resolution,[],[f101,f63])).
% 1.62/0.57  fof(f63,plain,(
% 1.62/0.57    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f46])).
% 1.62/0.57  fof(f101,plain,(
% 1.62/0.57    ~v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 1.62/0.57    inference(resolution,[],[f98,f64])).
% 1.62/0.57  fof(f64,plain,(
% 1.62/0.57    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f33])).
% 1.62/0.57  fof(f33,plain,(
% 1.62/0.57    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.62/0.57    inference(flattening,[],[f32])).
% 1.62/0.57  fof(f32,plain,(
% 1.62/0.57    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.62/0.57    inference(ennf_transformation,[],[f18])).
% 1.62/0.57  fof(f18,axiom,(
% 1.62/0.57    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).
% 1.62/0.57  fof(f98,plain,(
% 1.62/0.57    ~v1_xboole_0(k1_funct_2(sK0,sK1))),
% 1.62/0.57    inference(resolution,[],[f52,f62])).
% 1.62/0.57  fof(f308,plain,(
% 1.62/0.57    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 1.62/0.57    inference(backward_demodulation,[],[f106,f296])).
% 1.62/0.57  fof(f792,plain,(
% 1.62/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.62/0.57    inference(resolution,[],[f431,f89])).
% 1.62/0.57  fof(f89,plain,(
% 1.62/0.57    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.62/0.57    inference(equality_resolution,[],[f77])).
% 1.62/0.57  fof(f77,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f50])).
% 1.62/0.57  fof(f431,plain,(
% 1.62/0.57    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.62/0.57    inference(backward_demodulation,[],[f299,f427])).
% 1.62/0.57  fof(f299,plain,(
% 1.62/0.57    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 1.62/0.57    inference(backward_demodulation,[],[f96,f296])).
% 1.62/0.57  fof(f90,plain,(
% 1.62/0.57    k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2)),
% 1.62/0.57    inference(resolution,[],[f51,f59])).
% 1.62/0.57  fof(f843,plain,(
% 1.62/0.57    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 1.62/0.57    inference(trivial_inequality_removal,[],[f834])).
% 1.62/0.57  fof(f834,plain,(
% 1.62/0.57    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 1.62/0.57    inference(backward_demodulation,[],[f456,f831])).
% 1.62/0.57  fof(f456,plain,(
% 1.62/0.57    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK2)),
% 1.62/0.57    inference(subsumption_resolution,[],[f333,f427])).
% 1.62/0.57  fof(f333,plain,(
% 1.62/0.57    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | k1_xboole_0 != sK0 | k1_xboole_0 != k2_relat_1(sK2)),
% 1.62/0.57    inference(backward_demodulation,[],[f162,f296])).
% 1.62/0.57  fof(f162,plain,(
% 1.62/0.57    k1_xboole_0 != sK0 | ~r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 != k2_relat_1(sK2)),
% 1.62/0.57    inference(subsumption_resolution,[],[f160,f51])).
% 1.62/0.57  fof(f160,plain,(
% 1.62/0.57    k1_xboole_0 != sK0 | ~r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.57    inference(superposition,[],[f53,f60])).
% 1.62/0.57  fof(f60,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f42])).
% 1.62/0.57  % SZS output end Proof for theBenchmark
% 1.62/0.57  % (13858)------------------------------
% 1.62/0.57  % (13858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (13858)Termination reason: Refutation
% 1.62/0.57  
% 1.62/0.57  % (13858)Memory used [KB]: 1918
% 1.62/0.57  % (13858)Time elapsed: 0.146 s
% 1.62/0.57  % (13858)------------------------------
% 1.62/0.57  % (13858)------------------------------
% 1.62/0.57  % (13855)Success in time 0.212 s
%------------------------------------------------------------------------------
