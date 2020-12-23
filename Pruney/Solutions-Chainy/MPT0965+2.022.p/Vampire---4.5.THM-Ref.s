%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 225 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  300 (1047 expanded)
%              Number of equality atoms :   63 ( 222 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(subsumption_resolution,[],[f50,f325])).

fof(f325,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(resolution,[],[f324,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
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

fof(f324,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f323,f290])).

fof(f290,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f286,f50])).

fof(f286,plain,
    ( ~ r2_hidden(sK3,sK1)
    | v1_xboole_0(sK2) ),
    inference(backward_demodulation,[],[f203,f285])).

fof(f285,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f166,f284])).

fof(f284,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f283,f117])).

fof(f117,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),sK2)
    & k1_xboole_0 != sK2
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK3),sK2)
      & k1_xboole_0 != sK2
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f283,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ sP0(sK1,sK4,sK2) ),
    inference(subsumption_resolution,[],[f282,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f282,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f166,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f68,f49])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f203,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK4))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f202,f52])).

fof(f52,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK3),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f202,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK4,X0),sK2)
      | v1_xboole_0(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f201,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f201,plain,(
    ! [X0] :
      ( m1_subset_1(k1_funct_1(sK4,X0),sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f200,f108])).

fof(f108,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f69,f49])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK4,X1)
      | m1_subset_1(k1_funct_1(sK4,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f199,f94])).

fof(f94,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f91,f49])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | m1_subset_1(k1_funct_1(sK4,X0),X1)
      | ~ v5_relat_1(sK4,X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f77,f47])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f323,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f319,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f319,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f56,f309])).

fof(f309,plain,(
    sK1 = k1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f308,f98])).

fof(f98,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(k2_zfmisc_1(X1,X2)) = X1 ) ),
    inference(resolution,[],[f65,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f308,plain,(
    r1_tarski(sK1,k1_relat_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f305,f59])).

fof(f305,plain,
    ( r1_tarski(sK1,k1_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f300,f88])).

fof(f88,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f66,f49])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f300,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK4,X2)
      | r1_tarski(sK1,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f295,f94])).

fof(f295,plain,(
    ! [X2] :
      ( r1_tarski(sK1,k1_relat_1(X2))
      | ~ r1_tarski(sK4,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f53,f285])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f50,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:44:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (7830)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (7819)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (7824)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (7843)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (7834)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (7822)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (7826)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (7838)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (7832)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (7831)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (7825)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (7840)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (7825)Refutation not found, incomplete strategy% (7825)------------------------------
% 0.21/0.52  % (7825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7825)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7825)Memory used [KB]: 10618
% 0.21/0.52  % (7825)Time elapsed: 0.107 s
% 0.21/0.52  % (7825)------------------------------
% 0.21/0.52  % (7825)------------------------------
% 0.21/0.53  % (7832)Refutation not found, incomplete strategy% (7832)------------------------------
% 0.21/0.53  % (7832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7822)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (7833)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.28/0.53  % (7837)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.28/0.53  % (7842)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.28/0.54  % (7827)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.28/0.54  % (7823)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.28/0.54  % (7832)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (7832)Memory used [KB]: 6268
% 1.28/0.54  % (7832)Time elapsed: 0.120 s
% 1.28/0.54  % (7832)------------------------------
% 1.28/0.54  % (7832)------------------------------
% 1.28/0.54  % (7844)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.28/0.54  % (7841)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.28/0.55  % (7820)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.55  % SZS output start Proof for theBenchmark
% 1.28/0.55  fof(f326,plain,(
% 1.28/0.55    $false),
% 1.28/0.55    inference(subsumption_resolution,[],[f50,f325])).
% 1.28/0.55  fof(f325,plain,(
% 1.28/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 1.28/0.55    inference(resolution,[],[f324,f57])).
% 1.28/0.55  fof(f57,plain,(
% 1.28/0.55    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f40])).
% 1.28/0.55  fof(f40,plain,(
% 1.28/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.28/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 1.28/0.55  fof(f39,plain,(
% 1.28/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.28/0.55    introduced(choice_axiom,[])).
% 1.28/0.55  fof(f38,plain,(
% 1.28/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.28/0.55    inference(rectify,[],[f37])).
% 1.28/0.55  fof(f37,plain,(
% 1.28/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.28/0.55    inference(nnf_transformation,[],[f1])).
% 1.28/0.55  fof(f1,axiom,(
% 1.28/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.28/0.55  fof(f324,plain,(
% 1.28/0.55    v1_xboole_0(sK1)),
% 1.28/0.55    inference(subsumption_resolution,[],[f323,f290])).
% 1.28/0.55  fof(f290,plain,(
% 1.28/0.55    v1_xboole_0(sK2)),
% 1.28/0.55    inference(subsumption_resolution,[],[f286,f50])).
% 1.28/0.55  fof(f286,plain,(
% 1.28/0.55    ~r2_hidden(sK3,sK1) | v1_xboole_0(sK2)),
% 1.28/0.55    inference(backward_demodulation,[],[f203,f285])).
% 1.28/0.55  fof(f285,plain,(
% 1.28/0.55    sK1 = k1_relat_1(sK4)),
% 1.28/0.55    inference(backward_demodulation,[],[f166,f284])).
% 1.28/0.55  fof(f284,plain,(
% 1.28/0.55    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.28/0.55    inference(subsumption_resolution,[],[f283,f117])).
% 1.28/0.55  fof(f117,plain,(
% 1.28/0.55    sP0(sK1,sK4,sK2)),
% 1.28/0.55    inference(resolution,[],[f74,f49])).
% 1.28/0.55  fof(f49,plain,(
% 1.28/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.28/0.55    inference(cnf_transformation,[],[f36])).
% 1.28/0.55  fof(f36,plain,(
% 1.28/0.55    ~r2_hidden(k1_funct_1(sK4,sK3),sK2) & k1_xboole_0 != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 1.28/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f35])).
% 1.28/0.55  fof(f35,plain,(
% 1.28/0.55    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK4,sK3),sK2) & k1_xboole_0 != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.28/0.55    introduced(choice_axiom,[])).
% 1.28/0.55  fof(f19,plain,(
% 1.28/0.55    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.28/0.55    inference(flattening,[],[f18])).
% 1.28/0.55  fof(f18,plain,(
% 1.28/0.55    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.28/0.55    inference(ennf_transformation,[],[f16])).
% 1.28/0.55  fof(f16,negated_conjecture,(
% 1.28/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.28/0.55    inference(negated_conjecture,[],[f15])).
% 1.28/0.55  fof(f15,conjecture,(
% 1.28/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.28/0.55  fof(f74,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f46])).
% 1.28/0.55  fof(f46,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(nnf_transformation,[],[f34])).
% 1.28/0.55  fof(f34,plain,(
% 1.28/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(definition_folding,[],[f30,f33])).
% 1.28/0.55  fof(f33,plain,(
% 1.28/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.28/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.28/0.55  fof(f30,plain,(
% 1.28/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(flattening,[],[f29])).
% 1.28/0.55  fof(f29,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(ennf_transformation,[],[f14])).
% 1.28/0.55  fof(f14,axiom,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.28/0.55  fof(f283,plain,(
% 1.28/0.55    sK1 = k1_relset_1(sK1,sK2,sK4) | ~sP0(sK1,sK4,sK2)),
% 1.28/0.55    inference(subsumption_resolution,[],[f282,f51])).
% 1.28/0.55  fof(f51,plain,(
% 1.28/0.55    k1_xboole_0 != sK2),
% 1.28/0.55    inference(cnf_transformation,[],[f36])).
% 1.28/0.55  fof(f282,plain,(
% 1.28/0.55    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2 | ~sP0(sK1,sK4,sK2)),
% 1.28/0.55    inference(resolution,[],[f70,f48])).
% 1.28/0.55  fof(f48,plain,(
% 1.28/0.55    v1_funct_2(sK4,sK1,sK2)),
% 1.28/0.55    inference(cnf_transformation,[],[f36])).
% 1.28/0.55  fof(f70,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f45])).
% 1.28/0.55  fof(f45,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.28/0.55    inference(rectify,[],[f44])).
% 1.28/0.55  fof(f44,plain,(
% 1.28/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.28/0.55    inference(nnf_transformation,[],[f33])).
% 1.28/0.55  fof(f166,plain,(
% 1.28/0.55    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 1.28/0.55    inference(resolution,[],[f68,f49])).
% 1.28/0.55  fof(f68,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f27])).
% 1.28/0.55  fof(f27,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(ennf_transformation,[],[f13])).
% 1.28/0.55  fof(f13,axiom,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.28/0.55  fof(f203,plain,(
% 1.28/0.55    ~r2_hidden(sK3,k1_relat_1(sK4)) | v1_xboole_0(sK2)),
% 1.28/0.55    inference(resolution,[],[f202,f52])).
% 1.28/0.55  fof(f52,plain,(
% 1.28/0.55    ~r2_hidden(k1_funct_1(sK4,sK3),sK2)),
% 1.28/0.55    inference(cnf_transformation,[],[f36])).
% 1.28/0.55  fof(f202,plain,(
% 1.28/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),sK2) | v1_xboole_0(sK2) | ~r2_hidden(X0,k1_relat_1(sK4))) )),
% 1.28/0.55    inference(resolution,[],[f201,f62])).
% 1.28/0.55  fof(f62,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f26])).
% 1.28/0.55  fof(f26,plain,(
% 1.28/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.28/0.55    inference(flattening,[],[f25])).
% 1.28/0.55  fof(f25,plain,(
% 1.28/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.28/0.55    inference(ennf_transformation,[],[f4])).
% 1.28/0.55  fof(f4,axiom,(
% 1.28/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.28/0.55  fof(f201,plain,(
% 1.28/0.55    ( ! [X0] : (m1_subset_1(k1_funct_1(sK4,X0),sK2) | ~r2_hidden(X0,k1_relat_1(sK4))) )),
% 1.28/0.55    inference(resolution,[],[f200,f108])).
% 1.28/0.55  fof(f108,plain,(
% 1.28/0.55    v5_relat_1(sK4,sK2)),
% 1.28/0.55    inference(resolution,[],[f69,f49])).
% 1.28/0.55  fof(f69,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f28])).
% 1.28/0.55  fof(f28,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.55    inference(ennf_transformation,[],[f17])).
% 1.28/0.55  fof(f17,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.28/0.55    inference(pure_predicate_removal,[],[f12])).
% 1.28/0.55  fof(f12,axiom,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.28/0.55  fof(f200,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~v5_relat_1(sK4,X1) | m1_subset_1(k1_funct_1(sK4,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK4))) )),
% 1.28/0.55    inference(subsumption_resolution,[],[f199,f94])).
% 1.28/0.55  fof(f94,plain,(
% 1.28/0.55    v1_relat_1(sK4)),
% 1.28/0.55    inference(resolution,[],[f91,f49])).
% 1.28/0.55  fof(f91,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.28/0.55    inference(resolution,[],[f55,f59])).
% 1.28/0.55  fof(f59,plain,(
% 1.28/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.28/0.55    inference(cnf_transformation,[],[f8])).
% 1.28/0.55  fof(f8,axiom,(
% 1.28/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.28/0.55  fof(f55,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f22])).
% 1.28/0.55  fof(f22,plain,(
% 1.28/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.28/0.55    inference(ennf_transformation,[],[f6])).
% 1.28/0.55  fof(f6,axiom,(
% 1.28/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.28/0.55  fof(f199,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK4)) | m1_subset_1(k1_funct_1(sK4,X0),X1) | ~v5_relat_1(sK4,X1) | ~v1_relat_1(sK4)) )),
% 1.28/0.55    inference(resolution,[],[f77,f47])).
% 1.28/0.55  fof(f47,plain,(
% 1.28/0.55    v1_funct_1(sK4)),
% 1.28/0.55    inference(cnf_transformation,[],[f36])).
% 1.28/0.55  fof(f77,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f32])).
% 1.28/0.55  fof(f32,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 1.28/0.55    inference(flattening,[],[f31])).
% 1.28/0.55  fof(f31,plain,(
% 1.28/0.55    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 1.28/0.55    inference(ennf_transformation,[],[f11])).
% 1.28/0.55  fof(f11,axiom,(
% 1.28/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 1.28/0.55  fof(f323,plain,(
% 1.28/0.55    v1_xboole_0(sK1) | ~v1_xboole_0(sK2)),
% 1.28/0.55    inference(resolution,[],[f319,f61])).
% 1.28/0.55  fof(f61,plain,(
% 1.28/0.55    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f24])).
% 1.28/0.55  fof(f24,plain,(
% 1.28/0.55    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.28/0.55    inference(ennf_transformation,[],[f3])).
% 1.28/0.55  fof(f3,axiom,(
% 1.28/0.55    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.28/0.55  fof(f319,plain,(
% 1.28/0.55    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1)),
% 1.28/0.55    inference(superposition,[],[f56,f309])).
% 1.28/0.55  fof(f309,plain,(
% 1.28/0.55    sK1 = k1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 1.28/0.55    inference(resolution,[],[f308,f98])).
% 1.28/0.55  fof(f98,plain,(
% 1.28/0.55    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(k2_zfmisc_1(X1,X2)) = X1) )),
% 1.28/0.55    inference(resolution,[],[f65,f60])).
% 1.28/0.55  fof(f60,plain,(
% 1.28/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f9])).
% 1.28/0.55  fof(f9,axiom,(
% 1.28/0.55    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).
% 1.28/0.55  fof(f65,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.28/0.55    inference(cnf_transformation,[],[f42])).
% 1.28/0.55  fof(f42,plain,(
% 1.28/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.55    inference(flattening,[],[f41])).
% 1.28/0.55  fof(f41,plain,(
% 1.28/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.55    inference(nnf_transformation,[],[f2])).
% 1.28/0.55  fof(f2,axiom,(
% 1.28/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.28/0.55  fof(f308,plain,(
% 1.28/0.55    r1_tarski(sK1,k1_relat_1(k2_zfmisc_1(sK1,sK2)))),
% 1.28/0.55    inference(subsumption_resolution,[],[f305,f59])).
% 1.28/0.55  fof(f305,plain,(
% 1.28/0.55    r1_tarski(sK1,k1_relat_1(k2_zfmisc_1(sK1,sK2))) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 1.28/0.55    inference(resolution,[],[f300,f88])).
% 1.28/0.55  fof(f88,plain,(
% 1.28/0.55    r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))),
% 1.28/0.55    inference(resolution,[],[f66,f49])).
% 1.28/0.55  fof(f66,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f43])).
% 1.28/0.55  fof(f43,plain,(
% 1.28/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.28/0.55    inference(nnf_transformation,[],[f5])).
% 1.28/0.55  fof(f5,axiom,(
% 1.28/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.28/0.55  fof(f300,plain,(
% 1.28/0.55    ( ! [X2] : (~r1_tarski(sK4,X2) | r1_tarski(sK1,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.28/0.55    inference(subsumption_resolution,[],[f295,f94])).
% 1.28/0.55  fof(f295,plain,(
% 1.28/0.55    ( ! [X2] : (r1_tarski(sK1,k1_relat_1(X2)) | ~r1_tarski(sK4,X2) | ~v1_relat_1(X2) | ~v1_relat_1(sK4)) )),
% 1.28/0.55    inference(superposition,[],[f53,f285])).
% 1.28/0.55  fof(f53,plain,(
% 1.28/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f21])).
% 1.28/0.55  fof(f21,plain,(
% 1.28/0.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.28/0.55    inference(flattening,[],[f20])).
% 1.28/0.55  fof(f20,plain,(
% 1.28/0.55    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.28/0.55    inference(ennf_transformation,[],[f10])).
% 1.28/0.55  fof(f10,axiom,(
% 1.28/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.28/0.55  fof(f56,plain,(
% 1.28/0.55    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f23])).
% 1.28/0.55  fof(f23,plain,(
% 1.28/0.55    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.28/0.55    inference(ennf_transformation,[],[f7])).
% 1.28/0.55  fof(f7,axiom,(
% 1.28/0.55    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.28/0.55  fof(f50,plain,(
% 1.28/0.55    r2_hidden(sK3,sK1)),
% 1.28/0.55    inference(cnf_transformation,[],[f36])).
% 1.28/0.55  % SZS output end Proof for theBenchmark
% 1.28/0.55  % (7822)------------------------------
% 1.28/0.55  % (7822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (7822)Termination reason: Refutation
% 1.28/0.55  
% 1.28/0.55  % (7822)Memory used [KB]: 6524
% 1.28/0.55  % (7822)Time elapsed: 0.123 s
% 1.28/0.55  % (7822)------------------------------
% 1.28/0.55  % (7822)------------------------------
% 1.43/0.55  % (7818)Success in time 0.182 s
%------------------------------------------------------------------------------
