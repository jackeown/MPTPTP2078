%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 (1949 expanded)
%              Number of leaves         :   18 ( 569 expanded)
%              Depth                    :   34
%              Number of atoms          :  484 (13773 expanded)
%              Number of equality atoms :  186 (3085 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f663,plain,(
    $false ),
    inference(subsumption_resolution,[],[f660,f201])).

fof(f201,plain,(
    ! [X0] : r2_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f193,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f193,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f183,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(resolution,[],[f94,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f660,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f640,f652])).

fof(f652,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f651,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f651,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f650,f86])).

fof(f650,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0))
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f649,f566])).

fof(f566,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f550,f181])).

fof(f181,plain,(
    r2_relset_1(sK1,sK2,sK3,sK3) ),
    inference(resolution,[],[f94,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK3,X4)
              | ~ m1_subset_1(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK1,sK2,sK3,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK3,X4)
            | ~ m1_subset_1(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
      & ! [X4] :
          ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
          | ~ m1_subset_1(X4,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

fof(f550,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f56,f546])).

fof(f546,plain,
    ( sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f545,f335])).

fof(f335,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f333,f220])).

fof(f220,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f74,f51])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f333,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f330,f137])).

fof(f137,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f79,f51])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f330,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f545,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f544])).

fof(f544,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK3 = sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f543,f337])).

fof(f337,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f334,f221])).

fof(f221,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f74,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f334,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f331,f138])).

fof(f138,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f79,f54])).

fof(f331,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f75,f53])).

fof(f53,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f543,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f542,f105])).

fof(f105,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f51])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f542,plain,
    ( sK3 = sK4
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f541,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f541,plain,
    ( sK3 = sK4
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f540,f106])).

fof(f106,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f73,f54])).

fof(f540,plain,
    ( sK3 = sK4
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f539,f52])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f539,plain,
    ( sK3 = sK4
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f538])).

fof(f538,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK3,sK5(sK3,sK4))
    | sK3 = sK4
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f537])).

fof(f537,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK3,sK5(sK3,sK4))
    | sK3 = sK4
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | sK3 = sK4 ),
    inference(superposition,[],[f59,f527])).

fof(f527,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))
    | k1_xboole_0 = sK2
    | sK3 = sK4 ),
    inference(resolution,[],[f524,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ) ),
    inference(resolution,[],[f55,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f55,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f524,plain,
    ( r2_hidden(sK5(sK3,sK4),sK1)
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,
    ( r2_hidden(sK5(sK3,sK4),sK1)
    | sK3 = sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f520,f335])).

fof(f520,plain,
    ( r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3))
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f519,f335])).

fof(f519,plain,
    ( sK1 != k1_relat_1(sK3)
    | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3))
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f518,f337])).

fof(f518,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3))
    | sK3 = sK4 ),
    inference(subsumption_resolution,[],[f517,f106])).

fof(f517,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | sK3 = sK4 ),
    inference(resolution,[],[f402,f52])).

fof(f402,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | r2_hidden(sK5(sK3,X0),k1_relat_1(sK3))
      | ~ v1_relat_1(X0)
      | sK3 = X0 ) ),
    inference(subsumption_resolution,[],[f400,f105])).

fof(f400,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK3,X0),k1_relat_1(sK3))
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK3 = X0
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f58,f49])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f649,plain,
    ( k1_xboole_0 = sK4
    | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f579,f86])).

fof(f579,plain,
    ( sK4 = k2_zfmisc_1(sK1,k1_xboole_0)
    | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f164,f566])).

fof(f164,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | k2_zfmisc_1(sK1,sK2) = sK4 ),
    inference(resolution,[],[f114,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f66,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f114,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK4)
    | k2_zfmisc_1(sK1,sK2) = sK4 ),
    inference(resolution,[],[f64,f98])).

fof(f98,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f68,f54])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f640,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f571,f611])).

fof(f611,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f610,f57])).

fof(f610,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f609,f86])).

fof(f609,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0))
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f608,f566])).

fof(f608,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f578,f86])).

fof(f578,plain,
    ( sK3 = k2_zfmisc_1(sK1,k1_xboole_0)
    | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f163,f566])).

fof(f163,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(resolution,[],[f113,f101])).

fof(f113,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(resolution,[],[f64,f97])).

fof(f97,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f68,f51])).

fof(f571,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,sK3,sK4) ),
    inference(backward_demodulation,[],[f56,f566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:15:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (18457)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (18449)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (18441)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (18455)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (18438)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (18436)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (18434)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (18443)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (18453)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (18435)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (18437)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (18447)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (18442)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (18439)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (18462)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (18452)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (18451)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (18461)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (18454)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (18451)Refutation not found, incomplete strategy% (18451)------------------------------
% 0.20/0.55  % (18451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (18451)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (18451)Memory used [KB]: 10618
% 0.20/0.55  % (18451)Time elapsed: 0.138 s
% 0.20/0.55  % (18451)------------------------------
% 0.20/0.55  % (18451)------------------------------
% 0.20/0.55  % (18458)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (18444)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (18463)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (18459)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (18444)Refutation not found, incomplete strategy% (18444)------------------------------
% 0.20/0.56  % (18444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18444)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18444)Memory used [KB]: 10746
% 0.20/0.56  % (18444)Time elapsed: 0.150 s
% 0.20/0.56  % (18444)------------------------------
% 0.20/0.56  % (18444)------------------------------
% 0.20/0.56  % (18446)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (18445)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (18450)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (18460)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (18445)Refutation not found, incomplete strategy% (18445)------------------------------
% 0.20/0.56  % (18445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18445)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18445)Memory used [KB]: 10746
% 0.20/0.56  % (18445)Time elapsed: 0.150 s
% 0.20/0.56  % (18445)------------------------------
% 0.20/0.56  % (18445)------------------------------
% 0.20/0.57  % (18441)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f663,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(subsumption_resolution,[],[f660,f201])).
% 0.20/0.57  fof(f201,plain,(
% 0.20/0.57    ( ! [X0] : (r2_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )),
% 0.20/0.57    inference(superposition,[],[f193,f86])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f72])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.57    inference(flattening,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.57  fof(f193,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_relset_1(X0,X1,k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1))) )),
% 0.20/0.57    inference(resolution,[],[f183,f84])).
% 0.20/0.57  fof(f84,plain,(
% 0.20/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.57    inference(equality_resolution,[],[f63])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(flattening,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  fof(f183,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.20/0.57    inference(resolution,[],[f94,f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f93])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(equality_resolution,[],[f83])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.57  fof(f660,plain,(
% 0.20/0.57    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.57    inference(backward_demodulation,[],[f640,f652])).
% 0.20/0.57  fof(f652,plain,(
% 0.20/0.57    k1_xboole_0 = sK4),
% 0.20/0.57    inference(subsumption_resolution,[],[f651,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0)),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.57  fof(f651,plain,(
% 0.20/0.57    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK4),
% 0.20/0.57    inference(forward_demodulation,[],[f650,f86])).
% 0.20/0.57  fof(f650,plain,(
% 0.20/0.57    ~v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) | k1_xboole_0 = sK4),
% 0.20/0.57    inference(forward_demodulation,[],[f649,f566])).
% 0.20/0.57  fof(f566,plain,(
% 0.20/0.57    k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f550,f181])).
% 0.20/0.57  fof(f181,plain,(
% 0.20/0.57    r2_relset_1(sK1,sK2,sK3,sK3)),
% 0.20/0.57    inference(resolution,[],[f94,f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f32,f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.57    inference(negated_conjecture,[],[f13])).
% 0.20/0.57  fof(f13,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).
% 0.20/0.57  fof(f550,plain,(
% 0.20/0.57    ~r2_relset_1(sK1,sK2,sK3,sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(superposition,[],[f56,f546])).
% 0.20/0.57  fof(f546,plain,(
% 0.20/0.57    sK3 = sK4 | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f545,f335])).
% 0.20/0.57  fof(f335,plain,(
% 0.20/0.57    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(superposition,[],[f333,f220])).
% 0.20/0.57  fof(f220,plain,(
% 0.20/0.57    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f74,f51])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.57  fof(f333,plain,(
% 0.20/0.57    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f330,f137])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    sP0(sK1,sK3,sK2)),
% 0.20/0.57    inference(resolution,[],[f79,f51])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(definition_folding,[],[f26,f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.57  fof(f330,plain,(
% 0.20/0.57    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~sP0(sK1,sK3,sK2)),
% 0.20/0.57    inference(resolution,[],[f75,f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.20/0.57    inference(rectify,[],[f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f29])).
% 0.20/0.57  fof(f545,plain,(
% 0.20/0.57    sK1 != k1_relat_1(sK3) | sK3 = sK4 | k1_xboole_0 = sK2),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f544])).
% 0.20/0.57  fof(f544,plain,(
% 0.20/0.57    sK1 != k1_relat_1(sK3) | sK3 = sK4 | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.20/0.57    inference(superposition,[],[f543,f337])).
% 0.20/0.57  fof(f337,plain,(
% 0.20/0.57    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(superposition,[],[f334,f221])).
% 0.20/0.57  fof(f221,plain,(
% 0.20/0.57    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 0.20/0.57    inference(resolution,[],[f74,f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f334,plain,(
% 0.20/0.57    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f331,f138])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    sP0(sK1,sK4,sK2)),
% 0.20/0.57    inference(resolution,[],[f79,f54])).
% 0.20/0.57  fof(f331,plain,(
% 0.20/0.57    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2 | ~sP0(sK1,sK4,sK2)),
% 0.20/0.57    inference(resolution,[],[f75,f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    v1_funct_2(sK4,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f543,plain,(
% 0.20/0.57    k1_relat_1(sK3) != k1_relat_1(sK4) | sK3 = sK4 | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f542,f105])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f73,f51])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.57  fof(f542,plain,(
% 0.20/0.57    sK3 = sK4 | k1_relat_1(sK3) != k1_relat_1(sK4) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f541,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f541,plain,(
% 0.20/0.57    sK3 = sK4 | k1_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f540,f106])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    v1_relat_1(sK4)),
% 0.20/0.57    inference(resolution,[],[f73,f54])).
% 0.20/0.57  fof(f540,plain,(
% 0.20/0.57    sK3 = sK4 | k1_relat_1(sK3) != k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f539,f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    v1_funct_1(sK4)),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f539,plain,(
% 0.20/0.57    sK3 = sK4 | k1_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f538])).
% 0.20/0.57  fof(f538,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK3,sK5(sK3,sK4)) | sK3 = sK4 | k1_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f537])).
% 0.20/0.57  fof(f537,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK3,sK5(sK3,sK4)) | sK3 = sK4 | k1_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2 | sK3 = sK4),
% 0.20/0.57    inference(superposition,[],[f59,f527])).
% 0.20/0.57  fof(f527,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) | k1_xboole_0 = sK2 | sK3 = sK4),
% 0.20/0.57    inference(resolution,[],[f524,f136])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)) )),
% 0.20/0.57    inference(resolution,[],[f55,f61])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X4] : (~m1_subset_1(X4,sK1) | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f524,plain,(
% 0.20/0.57    r2_hidden(sK5(sK3,sK4),sK1) | sK3 = sK4 | k1_xboole_0 = sK2),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f523])).
% 0.20/0.57  fof(f523,plain,(
% 0.20/0.57    r2_hidden(sK5(sK3,sK4),sK1) | sK3 = sK4 | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.20/0.57    inference(superposition,[],[f520,f335])).
% 0.20/0.57  fof(f520,plain,(
% 0.20/0.57    r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3)) | sK3 = sK4 | k1_xboole_0 = sK2),
% 0.20/0.57    inference(subsumption_resolution,[],[f519,f335])).
% 0.20/0.57  fof(f519,plain,(
% 0.20/0.57    sK1 != k1_relat_1(sK3) | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3)) | sK3 = sK4 | k1_xboole_0 = sK2),
% 0.20/0.57    inference(superposition,[],[f518,f337])).
% 0.20/0.57  fof(f518,plain,(
% 0.20/0.57    k1_relat_1(sK3) != k1_relat_1(sK4) | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3)) | sK3 = sK4),
% 0.20/0.57    inference(subsumption_resolution,[],[f517,f106])).
% 0.20/0.57  fof(f517,plain,(
% 0.20/0.57    k1_relat_1(sK3) != k1_relat_1(sK4) | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3)) | ~v1_relat_1(sK4) | sK3 = sK4),
% 0.20/0.57    inference(resolution,[],[f402,f52])).
% 0.20/0.57  fof(f402,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | r2_hidden(sK5(sK3,X0),k1_relat_1(sK3)) | ~v1_relat_1(X0) | sK3 = X0) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f400,f105])).
% 0.20/0.57  fof(f400,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK5(sK3,X0),k1_relat_1(sK3)) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK3 = X0 | ~v1_relat_1(sK3)) )),
% 0.20/0.57    inference(resolution,[],[f58,f49])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f649,plain,(
% 0.20/0.57    k1_xboole_0 = sK4 | ~v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 0.20/0.57    inference(forward_demodulation,[],[f579,f86])).
% 0.20/0.57  fof(f579,plain,(
% 0.20/0.57    sK4 = k2_zfmisc_1(sK1,k1_xboole_0) | ~v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 0.20/0.57    inference(backward_demodulation,[],[f164,f566])).
% 0.20/0.57  fof(f164,plain,(
% 0.20/0.57    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | k2_zfmisc_1(sK1,sK2) = sK4),
% 0.20/0.57    inference(resolution,[],[f114,f101])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.57    inference(resolution,[],[f66,f60])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    ~r1_tarski(k2_zfmisc_1(sK1,sK2),sK4) | k2_zfmisc_1(sK1,sK2) = sK4),
% 0.20/0.57    inference(resolution,[],[f64,f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.57    inference(resolution,[],[f68,f54])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f42])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f640,plain,(
% 0.20/0.57    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4)),
% 0.20/0.57    inference(backward_demodulation,[],[f571,f611])).
% 0.20/0.57  fof(f611,plain,(
% 0.20/0.57    k1_xboole_0 = sK3),
% 0.20/0.57    inference(subsumption_resolution,[],[f610,f57])).
% 0.20/0.57  fof(f610,plain,(
% 0.20/0.57    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK3),
% 0.20/0.57    inference(forward_demodulation,[],[f609,f86])).
% 0.20/0.57  fof(f609,plain,(
% 0.20/0.57    ~v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) | k1_xboole_0 = sK3),
% 0.20/0.57    inference(forward_demodulation,[],[f608,f566])).
% 0.20/0.57  fof(f608,plain,(
% 0.20/0.57    k1_xboole_0 = sK3 | ~v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 0.20/0.57    inference(forward_demodulation,[],[f578,f86])).
% 0.20/0.57  fof(f578,plain,(
% 0.20/0.57    sK3 = k2_zfmisc_1(sK1,k1_xboole_0) | ~v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 0.20/0.57    inference(backward_demodulation,[],[f163,f566])).
% 0.20/0.57  fof(f163,plain,(
% 0.20/0.57    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 0.20/0.57    inference(resolution,[],[f113,f101])).
% 0.20/0.57  fof(f113,plain,(
% 0.20/0.57    ~r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 0.20/0.57    inference(resolution,[],[f64,f97])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.57    inference(resolution,[],[f68,f51])).
% 0.20/0.57  fof(f571,plain,(
% 0.20/0.57    ~r2_relset_1(sK1,k1_xboole_0,sK3,sK4)),
% 0.20/0.57    inference(backward_demodulation,[],[f56,f566])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (18441)------------------------------
% 0.20/0.57  % (18441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (18441)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (18441)Memory used [KB]: 6780
% 0.20/0.57  % (18441)Time elapsed: 0.105 s
% 0.20/0.57  % (18441)------------------------------
% 0.20/0.57  % (18441)------------------------------
% 0.20/0.58  % (18433)Success in time 0.213 s
%------------------------------------------------------------------------------
