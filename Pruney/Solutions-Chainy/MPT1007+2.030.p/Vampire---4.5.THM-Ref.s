%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 214 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  280 ( 777 expanded)
%              Number of equality atoms :   84 ( 190 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(subsumption_resolution,[],[f241,f59])).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f241,plain,(
    v1_xboole_0(k1_tarski(sK0)) ),
    inference(resolution,[],[f240,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f240,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f239,f55])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f239,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f238,f181])).

fof(f181,plain,(
    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) ),
    inference(backward_demodulation,[],[f53,f178])).

fof(f178,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f164,f176])).

fof(f176,plain,(
    k1_xboole_0 = k11_relat_1(sK2,sK0) ),
    inference(resolution,[],[f173,f137])).

fof(f137,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_relat_1(sK2))
      | k1_xboole_0 = k11_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f74,f87])).

fof(f87,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f173,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f169,f56])).

fof(f56,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f168,f87])).

fof(f168,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f166,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f75,f95])).

fof(f95,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f81,f54])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f164,plain,
    ( k1_xboole_0 != k11_relat_1(sK2,sK0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f162,f103])).

fof(f103,plain,(
    ! [X2] : k11_relat_1(sK2,X2) = k9_relat_1(sK2,k1_tarski(X2)) ),
    inference(resolution,[],[f65,f87])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f162,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k1_tarski(sK0))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f161,f87])).

fof(f161,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k9_relat_1(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f109,f117])).

fof(f117,plain,(
    sK2 = k7_relat_1(sK2,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f112,f87])).

fof(f112,plain,
    ( sK2 = k7_relat_1(sK2,k1_tarski(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f76,f93])).

fof(f93,plain,(
    v4_relat_1(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f80,f54])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X0))
      | k1_xboole_0 = k7_relat_1(sK2,X0)
      | k1_xboole_0 != k9_relat_1(sK2,X0) ) ),
    inference(superposition,[],[f64,f107])).

fof(f107,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f72,f87])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f53,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k1_xboole_0,X2,X0)
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f237,f84])).

fof(f84,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f77,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X1),k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | ~ v1_funct_2(k1_xboole_0,X2,X0) ) ),
    inference(forward_demodulation,[],[f236,f156])).

fof(f156,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_relset_1(X0,X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f154,f58])).

fof(f58,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f154,plain,(
    ! [X0,X1] : k2_relat_1(k1_xboole_0) = k2_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f79,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k1_funct_1(k1_xboole_0,X1),k2_relset_1(X2,X0,k1_xboole_0))
      | ~ v1_funct_2(k1_xboole_0,X2,X0) ) ),
    inference(subsumption_resolution,[],[f235,f100])).

fof(f100,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f68,f97])).

fof(f97,plain,(
    k1_xboole_0 = sK4(k1_xboole_0) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK4(X0) ) ),
    inference(superposition,[],[f88,f69])).

fof(f69,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_tarski(X2) = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = k1_tarski(X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_tarski(X2) = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k1_tarski(X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_tarski(X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK4(X0))
      | k1_xboole_0 = sK4(X0) ) ),
    inference(resolution,[],[f63,f67])).

fof(f67,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k1_funct_1(k1_xboole_0,X1),k2_relset_1(X2,X0,k1_xboole_0))
      | ~ v1_funct_2(k1_xboole_0,X2,X0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[],[f83,f61])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:44:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (12704)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (12711)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (12711)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f241,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    v1_xboole_0(k1_tarski(sK0))),
% 0.21/0.51    inference(resolution,[],[f240,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f239,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f21])).
% 0.21/0.51  fof(f21,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | k1_xboole_0 = sK1) )),
% 0.21/0.51    inference(resolution,[],[f238,f181])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)),
% 0.21/0.51    inference(backward_demodulation,[],[f53,f178])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    k1_xboole_0 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f164,f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    k1_xboole_0 = k11_relat_1(sK2,sK0)),
% 0.21/0.51    inference(resolution,[],[f173,f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X2] : (r2_hidden(X2,k1_relat_1(sK2)) | k1_xboole_0 = k11_relat_1(sK2,X2)) )),
% 0.21/0.51    inference(resolution,[],[f74,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f78,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f169,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f168,f87])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f166,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(resolution,[],[f75,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    v5_relat_1(sK2,sK1)),
% 0.21/0.51    inference(resolution,[],[f81,f54])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    k1_xboole_0 != k11_relat_1(sK2,sK0) | k1_xboole_0 = sK2),
% 0.21/0.51    inference(superposition,[],[f162,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X2] : (k11_relat_1(sK2,X2) = k9_relat_1(sK2,k1_tarski(X2))) )),
% 0.21/0.51    inference(resolution,[],[f65,f87])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    k1_xboole_0 != k9_relat_1(sK2,k1_tarski(sK0)) | k1_xboole_0 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f161,f87])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | k1_xboole_0 != k9_relat_1(sK2,k1_tarski(sK0))),
% 0.21/0.51    inference(superposition,[],[f109,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    sK2 = k7_relat_1(sK2,k1_tarski(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f87])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    sK2 = k7_relat_1(sK2,k1_tarski(sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f76,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    v4_relat_1(sK2,k1_tarski(sK0))),
% 0.21/0.51    inference(resolution,[],[f80,f54])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK2,X0)) | k1_xboole_0 = k7_relat_1(sK2,X0) | k1_xboole_0 != k9_relat_1(sK2,X0)) )),
% 0.21/0.51    inference(superposition,[],[f64,f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) )),
% 0.21/0.51    inference(resolution,[],[f72,f87])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(k1_xboole_0,X2,X0) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f237,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f77,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(k1_xboole_0,X1),k1_xboole_0) | k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | ~v1_funct_2(k1_xboole_0,X2,X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f236,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f154,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relat_1(k1_xboole_0) = k2_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f79,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | r2_hidden(k1_funct_1(k1_xboole_0,X1),k2_relset_1(X2,X0,k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,X2,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f235,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    v1_funct_1(k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f68,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    k1_xboole_0 = sK4(k1_xboole_0)),
% 0.21/0.51    inference(equality_resolution,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK4(X0)) )),
% 0.21/0.51    inference(superposition,[],[f88,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X0] : (! [X2] : (k1_tarski(X2) = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_tarski(X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_tarski(X2) = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_tarski(X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,axiom,(
% 0.21/0.51    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_tarski(X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK4(X0)) | k1_xboole_0 = sK4(X0)) )),
% 0.21/0.51    inference(resolution,[],[f63,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | r2_hidden(k1_funct_1(k1_xboole_0,X1),k2_relset_1(X2,X0,k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,X2,X0) | ~v1_funct_1(k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f83,f61])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12711)------------------------------
% 0.21/0.51  % (12711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12711)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12711)Memory used [KB]: 6396
% 0.21/0.51  % (12711)Time elapsed: 0.073 s
% 0.21/0.51  % (12711)------------------------------
% 0.21/0.51  % (12711)------------------------------
% 0.21/0.51  % (12703)Success in time 0.15 s
%------------------------------------------------------------------------------
