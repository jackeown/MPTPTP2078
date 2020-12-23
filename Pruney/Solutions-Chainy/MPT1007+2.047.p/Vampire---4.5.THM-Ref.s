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
% DateTime   : Thu Dec  3 13:03:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 146 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  314 ( 619 expanded)
%              Number of equality atoms :  116 ( 180 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(subsumption_resolution,[],[f156,f52])).

fof(f52,plain,(
    ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
      & v1_funct_2(sK5,k1_tarski(sK3),sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f156,plain,(
    r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
    inference(resolution,[],[f155,f96])).

fof(f96,plain,(
    v5_relat_1(sK5,sK4) ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f155,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK5,X0)
      | r2_hidden(k1_funct_1(sK5,sK3),X0) ) ),
    inference(subsumption_resolution,[],[f153,f95])).

fof(f95,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f153,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK5,sK3),X0)
      | ~ v5_relat_1(sK5,X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f151,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f151,plain,(
    r2_hidden(k1_funct_1(sK5,sK3),k2_relat_1(sK5)) ),
    inference(resolution,[],[f146,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK3))
      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) ) ),
    inference(subsumption_resolution,[],[f139,f95])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK3))
      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK3))
      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f55,f137])).

fof(f137,plain,(
    k1_tarski(sK3) = k1_relat_1(sK5) ),
    inference(backward_demodulation,[],[f99,f136])).

fof(f136,plain,(
    k1_tarski(sK3) = k1_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f135,plain,
    ( k1_xboole_0 = sK4
    | k1_tarski(sK3) = k1_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(subsumption_resolution,[],[f134,f49])).

fof(f49,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f134,plain,
    ( ~ v1_funct_2(sK5,k1_tarski(sK3),sK4)
    | k1_xboole_0 = sK4
    | k1_tarski(sK3) = k1_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(resolution,[],[f61,f97])).

fof(f97,plain,(
    sP0(k1_tarski(sK3),sK5,sK4) ),
    inference(resolution,[],[f65,f50])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(flattening,[],[f27])).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f99,plain,(
    k1_relat_1(sK5) = k1_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(resolution,[],[f59,f50])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f146,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f145,f89])).

fof(f89,plain,(
    ! [X4,X2,X5,X3,X1] : sP1(X1,X1,X2,X3,X4,X5) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP1(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP1(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP1(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP1(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( sP1(X6,X4,X3,X2,X1,X0)
    <=> ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f145,plain,(
    ! [X19,X18] :
      ( ~ sP1(X18,X19,X19,X19,X19,X19)
      | r2_hidden(X18,k1_tarski(X19)) ) ),
    inference(resolution,[],[f72,f102])).

fof(f102,plain,(
    ! [X0] : sP2(X0,X0,X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f101,f53])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f101,plain,(
    ! [X0,X1] : sP2(X0,X0,X0,X0,X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f100,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f100,plain,(
    ! [X2,X0,X1] : sP2(X0,X0,X0,X1,X2,k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f98,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : sP2(X0,X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f94,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] : sP2(X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP2(X0,X1,X2,X3,X4,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP2(X0,X1,X2,X3,X4,X5) )
      & ( sP2(X0,X1,X2,X3,X4,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(definition_folding,[],[f29,f33,f32])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP2(X0,X1,X2,X3,X4,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> sP1(X6,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3,X4,X5)
      | ~ sP1(X7,X4,X3,X2,X1,X0)
      | r2_hidden(X7,X5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP2(X0,X1,X2,X3,X4,X5)
        | ( ( ~ sP1(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5) )
          & ( sP1(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP1(X7,X4,X3,X2,X1,X0) )
            & ( sP1(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ~ sP1(X6,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X6,X5) )
          & ( sP1(X6,X4,X3,X2,X1,X0)
            | r2_hidden(X6,X5) ) )
     => ( ( ~ sP1(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5) )
        & ( sP1(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP2(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP1(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP1(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP1(X7,X4,X3,X2,X1,X0) )
            & ( sP1(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP2(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP1(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP1(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ~ sP1(X6,X4,X3,X2,X1,X0) )
            & ( sP1(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(nnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (15147)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.46  % (15155)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.48  % (15147)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f156,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK5,sK3),sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f15])).
% 0.21/0.48  fof(f15,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK5,sK3),sK4)),
% 0.21/0.48    inference(resolution,[],[f155,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    v5_relat_1(sK5,sK4)),
% 0.21/0.48    inference(resolution,[],[f60,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X0] : (~v5_relat_1(sK5,X0) | r2_hidden(k1_funct_1(sK5,sK3),X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    v1_relat_1(sK5)),
% 0.21/0.48    inference(resolution,[],[f58,f50])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(k1_funct_1(sK5,sK3),X0) | ~v5_relat_1(sK5,X0) | ~v1_relat_1(sK5)) )),
% 0.21/0.48    inference(resolution,[],[f151,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK5,sK3),k2_relat_1(sK5))),
% 0.21/0.48    inference(resolution,[],[f146,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK3)) | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f139,f95])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK3)) | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) | ~v1_relat_1(sK5)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    v1_funct_1(sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK3)) | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 0.21/0.48    inference(superposition,[],[f55,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    k1_tarski(sK3) = k1_relat_1(sK5)),
% 0.21/0.48    inference(backward_demodulation,[],[f99,f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    k1_tarski(sK3) = k1_relset_1(k1_tarski(sK3),sK4,sK5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    k1_xboole_0 != sK4),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    k1_xboole_0 = sK4 | k1_tarski(sK3) = k1_relset_1(k1_tarski(sK3),sK4,sK5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ~v1_funct_2(sK5,k1_tarski(sK3),sK4) | k1_xboole_0 = sK4 | k1_tarski(sK3) = k1_relset_1(k1_tarski(sK3),sK4,sK5)),
% 0.21/0.48    inference(resolution,[],[f61,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    sP0(k1_tarski(sK3),sK5,sK4)),
% 0.21/0.48    inference(resolution,[],[f65,f50])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(definition_folding,[],[f28,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.48    inference(rectify,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f30])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    k1_relat_1(sK5) = k1_relset_1(k1_tarski(sK3),sK4,sK5)),
% 0.21/0.48    inference(resolution,[],[f59,f50])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.21/0.48    inference(resolution,[],[f145,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X4,X2,X5,X3,X1] : (sP1(X1,X1,X2,X3,X4,X5)) )),
% 0.21/0.48    inference(equality_resolution,[],[f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 0.21/0.48    inference(rectify,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ! [X6,X4,X3,X2,X1,X0] : ((sP1(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~sP1(X6,X4,X3,X2,X1,X0)))),
% 0.21/0.48    inference(flattening,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X6,X4,X3,X2,X1,X0] : ((sP1(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~sP1(X6,X4,X3,X2,X1,X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X6,X4,X3,X2,X1,X0] : (sP1(X6,X4,X3,X2,X1,X0) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X19,X18] : (~sP1(X18,X19,X19,X19,X19,X19) | r2_hidden(X18,k1_tarski(X19))) )),
% 0.21/0.48    inference(resolution,[],[f72,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0] : (sP2(X0,X0,X0,X0,X0,k1_tarski(X0))) )),
% 0.21/0.48    inference(superposition,[],[f101,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP2(X0,X0,X0,X0,X1,k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(superposition,[],[f100,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP2(X0,X0,X0,X1,X2,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.48    inference(superposition,[],[f98,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (sP2(X0,X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3))) )),
% 0.21/0.48    inference(superposition,[],[f94,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (sP2(X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 0.21/0.48    inference(equality_resolution,[],[f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (sP2(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP2(X0,X1,X2,X3,X4,X5)) & (sP2(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.21/0.48    inference(nnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP2(X0,X1,X2,X3,X4,X5))),
% 0.21/0.48    inference(definition_folding,[],[f29,f33,f32])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (sP2(X0,X1,X2,X3,X4,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> sP1(X6,X4,X3,X2,X1,X0)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~sP2(X0,X1,X2,X3,X4,X5) | ~sP1(X7,X4,X3,X2,X1,X0) | r2_hidden(X7,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((sP2(X0,X1,X2,X3,X4,X5) | ((~sP1(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5)) & (sP1(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP1(X7,X4,X3,X2,X1,X0)) & (sP1(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP2(X0,X1,X2,X3,X4,X5)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : ((~sP1(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP1(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5))) => ((~sP1(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5)) & (sP1(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((sP2(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP1(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP1(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP1(X7,X4,X3,X2,X1,X0)) & (sP1(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP2(X0,X1,X2,X3,X4,X5)))),
% 0.21/0.48    inference(rectify,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((sP2(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP1(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP1(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | ~sP1(X6,X4,X3,X2,X1,X0)) & (sP1(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5))) | ~sP2(X0,X1,X2,X3,X4,X5)))),
% 0.21/0.48    inference(nnf_transformation,[],[f33])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (15147)------------------------------
% 0.21/0.48  % (15147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15147)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (15147)Memory used [KB]: 6396
% 0.21/0.48  % (15147)Time elapsed: 0.078 s
% 0.21/0.48  % (15147)------------------------------
% 0.21/0.48  % (15147)------------------------------
% 0.21/0.48  % (15139)Success in time 0.126 s
%------------------------------------------------------------------------------
