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
% DateTime   : Thu Dec  3 13:04:51 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 172 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  221 ( 450 expanded)
%              Number of equality atoms :   82 ( 166 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f520,plain,(
    $false ),
    inference(subsumption_resolution,[],[f519,f35])).

fof(f35,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f519,plain,(
    sK1 = k1_funct_1(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f516])).

fof(f516,plain,
    ( sK1 = k1_funct_1(sK3,sK2)
    | sK1 = k1_funct_1(sK3,sK2)
    | sK1 = k1_funct_1(sK3,sK2) ),
    inference(resolution,[],[f515,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f65,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f515,plain,(
    r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f504,f115])).

fof(f115,plain,(
    r1_tarski(k2_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f114,f107])).

fof(f107,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f52,f71])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f33,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f113,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

% (30298)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (30299)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f113,plain,(
    v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f54,f71])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f504,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | r2_hidden(k1_funct_1(sK3,sK2),X0) ) ),
    inference(resolution,[],[f500,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f500,plain,(
    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(resolution,[],[f496,f34])).

fof(f34,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f496,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f495,f107])).

fof(f495,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK3)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f494,f31])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f494,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) ) ),
    inference(superposition,[],[f82,f444])).

fof(f444,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f436,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f436,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | sK0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f102,f419])).

fof(f419,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f341,f159])).

fof(f159,plain,(
    k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f53,f71])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f341,plain,
    ( sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f340,f72])).

fof(f72,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f32,f70])).

fof(f32,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f340,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f60,f71])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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

fof(f102,plain,(
    ! [X2,X0,X1] : ~ r1_tarski(k2_enumset1(X0,X0,X1,X2),X2) ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f91,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k2_enumset1(X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f68,f51])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (30318)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (30310)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (30302)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (30301)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (30304)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.17/0.51  % (30300)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.51  % (30318)Refutation not found, incomplete strategy% (30318)------------------------------
% 1.17/0.51  % (30318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.51  % (30318)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.51  
% 1.17/0.51  % (30318)Memory used [KB]: 10874
% 1.17/0.51  % (30318)Time elapsed: 0.052 s
% 1.17/0.51  % (30318)------------------------------
% 1.17/0.51  % (30318)------------------------------
% 1.17/0.51  % (30296)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.17/0.52  % (30303)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.17/0.52  % (30307)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.17/0.52  % (30312)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.17/0.52  % (30320)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.17/0.53  % (30319)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.53  % (30297)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.53  % (30309)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.53  % (30325)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.53  % (30311)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.53  % (30302)Refutation found. Thanks to Tanya!
% 1.33/0.53  % SZS status Theorem for theBenchmark
% 1.33/0.53  % SZS output start Proof for theBenchmark
% 1.33/0.53  fof(f520,plain,(
% 1.33/0.53    $false),
% 1.33/0.53    inference(subsumption_resolution,[],[f519,f35])).
% 1.33/0.53  fof(f35,plain,(
% 1.33/0.53    sK1 != k1_funct_1(sK3,sK2)),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f19,plain,(
% 1.33/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.33/0.53    inference(flattening,[],[f18])).
% 1.33/0.53  fof(f18,plain,(
% 1.33/0.53    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.33/0.53    inference(ennf_transformation,[],[f16])).
% 1.33/0.53  fof(f16,negated_conjecture,(
% 1.33/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.33/0.53    inference(negated_conjecture,[],[f15])).
% 1.33/0.53  fof(f15,conjecture,(
% 1.33/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.33/0.53  fof(f519,plain,(
% 1.33/0.53    sK1 = k1_funct_1(sK3,sK2)),
% 1.33/0.53    inference(duplicate_literal_removal,[],[f516])).
% 1.33/0.53  fof(f516,plain,(
% 1.33/0.53    sK1 = k1_funct_1(sK3,sK2) | sK1 = k1_funct_1(sK3,sK2) | sK1 = k1_funct_1(sK3,sK2)),
% 1.33/0.53    inference(resolution,[],[f515,f96])).
% 1.33/0.53  fof(f96,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.33/0.53    inference(equality_resolution,[],[f76])).
% 1.33/0.53  fof(f76,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.33/0.53    inference(definition_unfolding,[],[f65,f51])).
% 1.33/0.53  fof(f51,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f5])).
% 1.33/0.53  fof(f5,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.33/0.53  fof(f65,plain,(
% 1.33/0.53    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.33/0.53    inference(cnf_transformation,[],[f30])).
% 1.33/0.53  fof(f30,plain,(
% 1.33/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.33/0.53    inference(ennf_transformation,[],[f2])).
% 1.33/0.53  fof(f2,axiom,(
% 1.33/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.33/0.53  fof(f515,plain,(
% 1.33/0.53    r2_hidden(k1_funct_1(sK3,sK2),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.33/0.53    inference(resolution,[],[f504,f115])).
% 1.33/0.53  fof(f115,plain,(
% 1.33/0.53    r1_tarski(k2_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.33/0.53    inference(subsumption_resolution,[],[f114,f107])).
% 1.33/0.53  fof(f107,plain,(
% 1.33/0.53    v1_relat_1(sK3)),
% 1.33/0.53    inference(resolution,[],[f52,f71])).
% 1.33/0.53  fof(f71,plain,(
% 1.33/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.33/0.53    inference(definition_unfolding,[],[f33,f70])).
% 1.33/0.53  fof(f70,plain,(
% 1.33/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.33/0.53    inference(definition_unfolding,[],[f37,f69])).
% 1.33/0.53  fof(f69,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.33/0.53    inference(definition_unfolding,[],[f44,f51])).
% 1.33/0.53  fof(f44,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f4])).
% 1.33/0.53  fof(f4,axiom,(
% 1.33/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.33/0.53  fof(f37,plain,(
% 1.33/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f3])).
% 1.33/0.53  fof(f3,axiom,(
% 1.33/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.33/0.53  fof(f33,plain,(
% 1.33/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f52,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f25])).
% 1.33/0.53  fof(f25,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.53    inference(ennf_transformation,[],[f11])).
% 1.33/0.53  fof(f11,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.33/0.53  fof(f114,plain,(
% 1.33/0.53    r1_tarski(k2_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_relat_1(sK3)),
% 1.33/0.53    inference(resolution,[],[f113,f46])).
% 1.33/0.53  fof(f46,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f22])).
% 1.33/0.53  fof(f22,plain,(
% 1.33/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.33/0.53    inference(ennf_transformation,[],[f8])).
% 1.33/0.53  fof(f8,axiom,(
% 1.33/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.33/0.53  % (30298)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.53  % (30299)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.53  fof(f113,plain,(
% 1.33/0.53    v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.33/0.53    inference(resolution,[],[f54,f71])).
% 1.33/0.53  fof(f54,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f27])).
% 1.33/0.53  fof(f27,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.53    inference(ennf_transformation,[],[f17])).
% 1.33/0.53  fof(f17,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.33/0.53    inference(pure_predicate_removal,[],[f12])).
% 1.33/0.53  fof(f12,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.33/0.53  fof(f504,plain,(
% 1.33/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | r2_hidden(k1_funct_1(sK3,sK2),X0)) )),
% 1.33/0.53    inference(resolution,[],[f500,f130])).
% 1.33/0.53  fof(f130,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~r1_tarski(X1,X2)) )),
% 1.33/0.53    inference(resolution,[],[f47,f48])).
% 1.33/0.53  fof(f48,plain,(
% 1.33/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f7])).
% 1.33/0.53  fof(f7,axiom,(
% 1.33/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.33/0.53  fof(f47,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f23])).
% 1.33/0.53  fof(f23,plain,(
% 1.33/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f6])).
% 1.33/0.53  fof(f6,axiom,(
% 1.33/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.33/0.53  fof(f500,plain,(
% 1.33/0.53    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 1.33/0.53    inference(resolution,[],[f496,f34])).
% 1.33/0.53  fof(f34,plain,(
% 1.33/0.53    r2_hidden(sK2,sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f496,plain,(
% 1.33/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f495,f107])).
% 1.33/0.53  fof(f495,plain,(
% 1.33/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f494,f31])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    v1_funct_1(sK3)),
% 1.33/0.54    inference(cnf_transformation,[],[f19])).
% 1.33/0.54  fof(f494,plain,(
% 1.33/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) )),
% 1.33/0.54    inference(superposition,[],[f82,f444])).
% 1.33/0.54  fof(f444,plain,(
% 1.33/0.54    sK0 = k1_relat_1(sK3)),
% 1.33/0.54    inference(subsumption_resolution,[],[f436,f36])).
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.33/0.54  fof(f436,plain,(
% 1.33/0.54    ~r1_tarski(k1_xboole_0,sK1) | sK0 = k1_relat_1(sK3)),
% 1.33/0.54    inference(superposition,[],[f102,f419])).
% 1.33/0.54  fof(f419,plain,(
% 1.33/0.54    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relat_1(sK3)),
% 1.33/0.54    inference(superposition,[],[f341,f159])).
% 1.33/0.54  fof(f159,plain,(
% 1.33/0.54    k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) = k1_relat_1(sK3)),
% 1.33/0.54    inference(resolution,[],[f53,f71])).
% 1.33/0.54  fof(f53,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f26])).
% 1.33/0.54  fof(f26,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.54    inference(ennf_transformation,[],[f13])).
% 1.33/0.54  fof(f13,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.33/0.54  fof(f341,plain,(
% 1.33/0.54    sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.33/0.54    inference(subsumption_resolution,[],[f340,f72])).
% 1.33/0.54  fof(f72,plain,(
% 1.33/0.54    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.33/0.54    inference(definition_unfolding,[],[f32,f70])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.33/0.54    inference(cnf_transformation,[],[f19])).
% 1.33/0.54  fof(f340,plain,(
% 1.33/0.54    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.33/0.54    inference(resolution,[],[f60,f71])).
% 1.33/0.54  fof(f60,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f29])).
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.54    inference(flattening,[],[f28])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.54    inference(ennf_transformation,[],[f14])).
% 1.33/0.54  fof(f14,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.33/0.54  fof(f102,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X1,X2),X2)) )),
% 1.33/0.54    inference(resolution,[],[f91,f50])).
% 1.33/0.54  fof(f50,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f24])).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.33/0.54    inference(ennf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,axiom,(
% 1.33/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.33/0.54  fof(f91,plain,(
% 1.33/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X4))) )),
% 1.33/0.54    inference(equality_resolution,[],[f90])).
% 1.33/0.54  fof(f90,plain,(
% 1.33/0.54    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X4) != X3) )),
% 1.33/0.54    inference(equality_resolution,[],[f73])).
% 1.33/0.54  fof(f73,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.33/0.54    inference(definition_unfolding,[],[f68,f51])).
% 1.33/0.54  fof(f68,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.33/0.54    inference(cnf_transformation,[],[f30])).
% 1.33/0.54  fof(f82,plain,(
% 1.33/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))) )),
% 1.33/0.54    inference(equality_resolution,[],[f81])).
% 1.33/0.54  fof(f81,plain,(
% 1.33/0.54    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.33/0.54    inference(equality_resolution,[],[f43])).
% 1.33/0.54  fof(f43,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.54    inference(flattening,[],[f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f9])).
% 1.33/0.54  fof(f9,axiom,(
% 1.33/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (30302)------------------------------
% 1.33/0.54  % (30302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (30302)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (30302)Memory used [KB]: 6652
% 1.33/0.54  % (30302)Time elapsed: 0.083 s
% 1.33/0.54  % (30302)------------------------------
% 1.33/0.54  % (30302)------------------------------
% 1.33/0.54  % (30316)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.54  % (30295)Success in time 0.179 s
%------------------------------------------------------------------------------
