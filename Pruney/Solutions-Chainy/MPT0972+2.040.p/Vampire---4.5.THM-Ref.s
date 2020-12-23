%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:10 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  130 (1270 expanded)
%              Number of leaves         :   20 ( 372 expanded)
%              Depth                    :   33
%              Number of atoms          :  479 (8624 expanded)
%              Number of equality atoms :  175 (1880 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1299,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1238,f190])).

fof(f190,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f110,f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1238,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1019,f1182])).

fof(f1182,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f1174,f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f134,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f83,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f131,f68])).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f81,f119])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1174,plain,(
    v1_xboole_0(sK4) ),
    inference(resolution,[],[f879,f173])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f172,f102])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f76,f68])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f879,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f868,f102])).

fof(f868,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f65,f864])).

fof(f864,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f829,f191])).

fof(f191,plain,(
    r2_relset_1(sK1,sK2,sK3,sK3) ),
    inference(resolution,[],[f110,f62])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ r2_hidden(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
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
              | ~ r2_hidden(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK1,sK2,sK3,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK3,X4)
            | ~ r2_hidden(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
      & ! [X4] :
          ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
          | ~ r2_hidden(X4,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f829,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f67,f825])).

fof(f825,plain,
    ( sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f824,f316])).

fof(f316,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f313,f196])).

fof(f196,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f88,f62])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f313,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f310,f61])).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f310,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f90,f176])).

fof(f176,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f94,f62])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f31,f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f824,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f823])).

fof(f823,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK3 = sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f822,f325])).

fof(f325,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f314,f197])).

fof(f197,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f88,f65])).

fof(f314,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f311,f64])).

fof(f64,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f311,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f90,f177])).

fof(f177,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f94,f65])).

fof(f822,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK3)
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f821,f123])).

fof(f123,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f116,f62])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f70,f75])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f70,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f821,plain,
    ( sK3 = sK4
    | k1_relat_1(sK4) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f820,f60])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f820,plain,
    ( sK3 = sK4
    | k1_relat_1(sK4) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f819,f124])).

fof(f124,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f116,f65])).

fof(f819,plain,
    ( sK3 = sK4
    | k1_relat_1(sK4) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f818,f63])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f818,plain,
    ( sK3 = sK4
    | k1_relat_1(sK4) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f817])).

fof(f817,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK3,sK5(sK3,sK4))
    | sK3 = sK4
    | k1_relat_1(sK4) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f816])).

fof(f816,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK3,sK5(sK3,sK4))
    | sK3 = sK4
    | k1_relat_1(sK4) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | sK3 = sK4 ),
    inference(superposition,[],[f72,f769])).

fof(f769,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))
    | k1_xboole_0 = sK2
    | sK3 = sK4 ),
    inference(resolution,[],[f760,f66])).

fof(f66,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f760,plain,
    ( r2_hidden(sK5(sK3,sK4),sK1)
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f759])).

fof(f759,plain,
    ( r2_hidden(sK5(sK3,sK4),sK1)
    | sK3 = sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f756,f316])).

fof(f756,plain,
    ( r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3))
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f755,f316])).

fof(f755,plain,
    ( sK1 != k1_relat_1(sK3)
    | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3))
    | sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f754,f325])).

fof(f754,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK3)
    | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3))
    | sK3 = sK4 ),
    inference(subsumption_resolution,[],[f753,f124])).

fof(f753,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK3)
    | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | sK3 = sK4 ),
    inference(resolution,[],[f400,f63])).

fof(f400,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | r2_hidden(sK5(sK3,X0),k1_relat_1(sK3))
      | ~ v1_relat_1(X0)
      | sK3 = X0 ) ),
    inference(subsumption_resolution,[],[f398,f123])).

fof(f398,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK3,X0),k1_relat_1(sK3))
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK3 = X0
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f71,f60])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f1019,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f869,f893])).

fof(f893,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f885,f135])).

fof(f885,plain,(
    v1_xboole_0(sK3) ),
    inference(resolution,[],[f878,f173])).

fof(f878,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f866,f102])).

fof(f866,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f62,f864])).

fof(f869,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,sK3,sK4) ),
    inference(backward_demodulation,[],[f67,f864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (10546)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (10547)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (10562)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (10554)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (10555)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (10563)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.58  % (10543)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.67/0.60  % (10545)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.67/0.60  % (10540)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.67/0.60  % (10542)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.67/0.61  % (10561)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.67/0.61  % (10556)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.67/0.61  % (10558)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.67/0.61  % (10549)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.67/0.61  % (10567)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.67/0.61  % (10565)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.67/0.61  % (10553)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.67/0.61  % (10557)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.67/0.62  % (10564)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.67/0.62  % (10566)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.67/0.62  % (10551)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.67/0.62  % (10569)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.67/0.62  % (10541)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.67/0.62  % (10550)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.67/0.62  % (10548)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.67/0.63  % (10559)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.67/0.63  % (10562)Refutation not found, incomplete strategy% (10562)------------------------------
% 1.67/0.63  % (10562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.63  % (10562)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.63  
% 1.67/0.63  % (10562)Memory used [KB]: 11001
% 1.67/0.63  % (10562)Time elapsed: 0.194 s
% 1.67/0.63  % (10562)------------------------------
% 1.67/0.63  % (10562)------------------------------
% 1.67/0.63  % (10550)Refutation not found, incomplete strategy% (10550)------------------------------
% 1.67/0.63  % (10550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.63  % (10550)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.63  
% 1.67/0.63  % (10550)Memory used [KB]: 10746
% 1.67/0.63  % (10550)Time elapsed: 0.194 s
% 1.67/0.63  % (10550)------------------------------
% 1.67/0.63  % (10550)------------------------------
% 1.67/0.63  % (10544)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.67/0.63  % (10542)Refutation not found, incomplete strategy% (10542)------------------------------
% 1.67/0.63  % (10542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.63  % (10542)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.63  
% 1.67/0.63  % (10542)Memory used [KB]: 10874
% 1.67/0.63  % (10542)Time elapsed: 0.196 s
% 1.67/0.63  % (10542)------------------------------
% 1.67/0.63  % (10542)------------------------------
% 1.67/0.64  % (10568)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.67/0.64  % (10552)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.67/0.64  % (10560)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.67/0.65  % (10548)Refutation not found, incomplete strategy% (10548)------------------------------
% 1.67/0.65  % (10548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.65  % (10548)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.65  
% 1.67/0.65  % (10548)Memory used [KB]: 10746
% 1.67/0.65  % (10548)Time elapsed: 0.222 s
% 1.67/0.65  % (10548)------------------------------
% 1.67/0.65  % (10548)------------------------------
% 1.67/0.66  % (10547)Refutation found. Thanks to Tanya!
% 1.67/0.66  % SZS status Theorem for theBenchmark
% 1.67/0.66  % SZS output start Proof for theBenchmark
% 1.67/0.66  fof(f1299,plain,(
% 1.67/0.66    $false),
% 1.67/0.66    inference(subsumption_resolution,[],[f1238,f190])).
% 1.67/0.66  fof(f190,plain,(
% 1.67/0.66    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 1.67/0.66    inference(resolution,[],[f110,f69])).
% 1.67/0.66  fof(f69,plain,(
% 1.67/0.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.67/0.66    inference(cnf_transformation,[],[f6])).
% 1.67/0.66  fof(f6,axiom,(
% 1.67/0.66    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.67/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.67/0.66  fof(f110,plain,(
% 1.67/0.66    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.67/0.66    inference(duplicate_literal_removal,[],[f109])).
% 1.67/0.66  fof(f109,plain,(
% 1.67/0.66    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.66    inference(equality_resolution,[],[f99])).
% 1.67/0.66  fof(f99,plain,(
% 1.67/0.66    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.66    inference(cnf_transformation,[],[f59])).
% 1.67/0.66  fof(f59,plain,(
% 1.67/0.66    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.66    inference(nnf_transformation,[],[f35])).
% 1.67/0.66  fof(f35,plain,(
% 1.67/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.66    inference(flattening,[],[f34])).
% 1.67/0.66  fof(f34,plain,(
% 1.67/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.67/0.66    inference(ennf_transformation,[],[f15])).
% 2.25/0.67  fof(f15,axiom,(
% 2.25/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.25/0.67  fof(f1238,plain,(
% 2.25/0.67    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.25/0.67    inference(backward_demodulation,[],[f1019,f1182])).
% 2.25/0.67  fof(f1182,plain,(
% 2.25/0.67    k1_xboole_0 = sK4),
% 2.25/0.67    inference(resolution,[],[f1174,f135])).
% 2.25/0.67  fof(f135,plain,(
% 2.25/0.67    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.25/0.67    inference(resolution,[],[f134,f119])).
% 2.25/0.67  fof(f119,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.25/0.67    inference(resolution,[],[f83,f73])).
% 2.25/0.67  fof(f73,plain,(
% 2.25/0.67    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f46])).
% 2.25/0.67  fof(f46,plain,(
% 2.25/0.67    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.25/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 2.25/0.67  fof(f45,plain,(
% 2.25/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 2.25/0.67    introduced(choice_axiom,[])).
% 2.25/0.67  fof(f44,plain,(
% 2.25/0.67    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.25/0.67    inference(rectify,[],[f43])).
% 2.25/0.67  fof(f43,plain,(
% 2.25/0.67    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.25/0.67    inference(nnf_transformation,[],[f1])).
% 2.25/0.67  fof(f1,axiom,(
% 2.25/0.67    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.25/0.67  fof(f83,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f53])).
% 2.25/0.67  fof(f53,plain,(
% 2.25/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.25/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).
% 2.25/0.67  fof(f52,plain,(
% 2.25/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 2.25/0.67    introduced(choice_axiom,[])).
% 2.25/0.67  fof(f51,plain,(
% 2.25/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.25/0.67    inference(rectify,[],[f50])).
% 2.25/0.67  fof(f50,plain,(
% 2.25/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.25/0.67    inference(nnf_transformation,[],[f27])).
% 2.25/0.67  fof(f27,plain,(
% 2.25/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.25/0.67    inference(ennf_transformation,[],[f2])).
% 2.25/0.67  fof(f2,axiom,(
% 2.25/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.25/0.67  fof(f134,plain,(
% 2.25/0.67    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.25/0.67    inference(resolution,[],[f131,f68])).
% 2.25/0.67  fof(f68,plain,(
% 2.25/0.67    v1_xboole_0(k1_xboole_0)),
% 2.25/0.67    inference(cnf_transformation,[],[f3])).
% 2.25/0.67  fof(f3,axiom,(
% 2.25/0.67    v1_xboole_0(k1_xboole_0)),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.25/0.67  fof(f131,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.25/0.67    inference(resolution,[],[f81,f119])).
% 2.25/0.67  fof(f81,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.25/0.67    inference(cnf_transformation,[],[f49])).
% 2.25/0.67  fof(f49,plain,(
% 2.25/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.25/0.67    inference(flattening,[],[f48])).
% 2.25/0.67  fof(f48,plain,(
% 2.25/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.25/0.67    inference(nnf_transformation,[],[f4])).
% 2.25/0.67  fof(f4,axiom,(
% 2.25/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.25/0.67  fof(f1174,plain,(
% 2.25/0.67    v1_xboole_0(sK4)),
% 2.25/0.67    inference(resolution,[],[f879,f173])).
% 2.25/0.67  fof(f173,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 2.25/0.67    inference(forward_demodulation,[],[f172,f102])).
% 2.25/0.67  fof(f102,plain,(
% 2.25/0.67    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.25/0.67    inference(equality_resolution,[],[f87])).
% 2.25/0.67  fof(f87,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.25/0.67    inference(cnf_transformation,[],[f55])).
% 2.25/0.67  fof(f55,plain,(
% 2.25/0.67    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.25/0.67    inference(flattening,[],[f54])).
% 2.25/0.67  fof(f54,plain,(
% 2.25/0.67    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.25/0.67    inference(nnf_transformation,[],[f5])).
% 2.25/0.67  fof(f5,axiom,(
% 2.25/0.67    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.25/0.67  fof(f172,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 2.25/0.67    inference(resolution,[],[f76,f68])).
% 2.25/0.67  fof(f76,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f25])).
% 2.25/0.67  fof(f25,plain,(
% 2.25/0.67    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.25/0.67    inference(ennf_transformation,[],[f13])).
% 2.25/0.67  fof(f13,axiom,(
% 2.25/0.67    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 2.25/0.67  fof(f879,plain,(
% 2.25/0.67    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 2.25/0.67    inference(forward_demodulation,[],[f868,f102])).
% 2.25/0.67  fof(f868,plain,(
% 2.25/0.67    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 2.25/0.67    inference(backward_demodulation,[],[f65,f864])).
% 2.25/0.67  fof(f864,plain,(
% 2.25/0.67    k1_xboole_0 = sK2),
% 2.25/0.67    inference(subsumption_resolution,[],[f829,f191])).
% 2.25/0.67  fof(f191,plain,(
% 2.25/0.67    r2_relset_1(sK1,sK2,sK3,sK3)),
% 2.25/0.67    inference(resolution,[],[f110,f62])).
% 2.25/0.67  fof(f62,plain,(
% 2.25/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.25/0.67    inference(cnf_transformation,[],[f40])).
% 2.25/0.67  fof(f40,plain,(
% 2.25/0.67    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.25/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f39,f38])).
% 2.25/0.67  fof(f38,plain,(
% 2.25/0.67    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.25/0.67    introduced(choice_axiom,[])).
% 2.25/0.67  fof(f39,plain,(
% 2.25/0.67    ? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 2.25/0.67    introduced(choice_axiom,[])).
% 2.25/0.67  fof(f21,plain,(
% 2.25/0.67    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.25/0.67    inference(flattening,[],[f20])).
% 2.25/0.67  fof(f20,plain,(
% 2.25/0.67    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.25/0.67    inference(ennf_transformation,[],[f18])).
% 2.25/0.67  fof(f18,negated_conjecture,(
% 2.25/0.67    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.25/0.67    inference(negated_conjecture,[],[f17])).
% 2.25/0.67  fof(f17,conjecture,(
% 2.25/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 2.25/0.67  fof(f829,plain,(
% 2.25/0.67    ~r2_relset_1(sK1,sK2,sK3,sK3) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(superposition,[],[f67,f825])).
% 2.25/0.67  fof(f825,plain,(
% 2.25/0.67    sK3 = sK4 | k1_xboole_0 = sK2),
% 2.25/0.67    inference(subsumption_resolution,[],[f824,f316])).
% 2.25/0.67  fof(f316,plain,(
% 2.25/0.67    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(superposition,[],[f313,f196])).
% 2.25/0.67  fof(f196,plain,(
% 2.25/0.67    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 2.25/0.67    inference(resolution,[],[f88,f62])).
% 2.25/0.67  fof(f88,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f28])).
% 2.25/0.67  fof(f28,plain,(
% 2.25/0.67    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.67    inference(ennf_transformation,[],[f14])).
% 2.25/0.67  fof(f14,axiom,(
% 2.25/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.25/0.67  fof(f313,plain,(
% 2.25/0.67    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(subsumption_resolution,[],[f310,f61])).
% 2.25/0.67  fof(f61,plain,(
% 2.25/0.67    v1_funct_2(sK3,sK1,sK2)),
% 2.25/0.67    inference(cnf_transformation,[],[f40])).
% 2.25/0.67  fof(f310,plain,(
% 2.25/0.67    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 2.25/0.67    inference(resolution,[],[f90,f176])).
% 2.25/0.67  fof(f176,plain,(
% 2.25/0.67    sP0(sK1,sK3,sK2)),
% 2.25/0.67    inference(resolution,[],[f94,f62])).
% 2.25/0.67  fof(f94,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f58])).
% 2.25/0.67  fof(f58,plain,(
% 2.25/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.67    inference(nnf_transformation,[],[f37])).
% 2.25/0.67  fof(f37,plain,(
% 2.25/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.67    inference(definition_folding,[],[f31,f36])).
% 2.25/0.67  fof(f36,plain,(
% 2.25/0.67    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 2.25/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.25/0.67  fof(f31,plain,(
% 2.25/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.67    inference(flattening,[],[f30])).
% 2.25/0.67  fof(f30,plain,(
% 2.25/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.67    inference(ennf_transformation,[],[f16])).
% 2.25/0.67  fof(f16,axiom,(
% 2.25/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.25/0.67  fof(f90,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 2.25/0.67    inference(cnf_transformation,[],[f57])).
% 2.25/0.67  fof(f57,plain,(
% 2.25/0.67    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 2.25/0.67    inference(rectify,[],[f56])).
% 2.25/0.67  fof(f56,plain,(
% 2.25/0.67    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 2.25/0.67    inference(nnf_transformation,[],[f36])).
% 2.25/0.67  fof(f824,plain,(
% 2.25/0.67    sK1 != k1_relat_1(sK3) | sK3 = sK4 | k1_xboole_0 = sK2),
% 2.25/0.67    inference(duplicate_literal_removal,[],[f823])).
% 2.25/0.67  fof(f823,plain,(
% 2.25/0.67    sK1 != k1_relat_1(sK3) | sK3 = sK4 | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 2.25/0.67    inference(superposition,[],[f822,f325])).
% 2.25/0.67  fof(f325,plain,(
% 2.25/0.67    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(superposition,[],[f314,f197])).
% 2.25/0.67  fof(f197,plain,(
% 2.25/0.67    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 2.25/0.67    inference(resolution,[],[f88,f65])).
% 2.25/0.67  fof(f314,plain,(
% 2.25/0.67    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(subsumption_resolution,[],[f311,f64])).
% 2.25/0.67  fof(f64,plain,(
% 2.25/0.67    v1_funct_2(sK4,sK1,sK2)),
% 2.25/0.67    inference(cnf_transformation,[],[f40])).
% 2.25/0.67  fof(f311,plain,(
% 2.25/0.67    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 2.25/0.67    inference(resolution,[],[f90,f177])).
% 2.25/0.67  fof(f177,plain,(
% 2.25/0.67    sP0(sK1,sK4,sK2)),
% 2.25/0.67    inference(resolution,[],[f94,f65])).
% 2.25/0.67  fof(f822,plain,(
% 2.25/0.67    k1_relat_1(sK4) != k1_relat_1(sK3) | sK3 = sK4 | k1_xboole_0 = sK2),
% 2.25/0.67    inference(subsumption_resolution,[],[f821,f123])).
% 2.25/0.67  fof(f123,plain,(
% 2.25/0.67    v1_relat_1(sK3)),
% 2.25/0.67    inference(resolution,[],[f116,f62])).
% 2.25/0.67  fof(f116,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 2.25/0.67    inference(resolution,[],[f70,f75])).
% 2.25/0.67  fof(f75,plain,(
% 2.25/0.67    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f10])).
% 2.25/0.67  fof(f10,axiom,(
% 2.25/0.67    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.25/0.67  fof(f70,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f22])).
% 2.25/0.67  fof(f22,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.25/0.67    inference(ennf_transformation,[],[f8])).
% 2.25/0.67  fof(f8,axiom,(
% 2.25/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.25/0.67  fof(f821,plain,(
% 2.25/0.67    sK3 = sK4 | k1_relat_1(sK4) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(subsumption_resolution,[],[f820,f60])).
% 2.25/0.67  fof(f60,plain,(
% 2.25/0.67    v1_funct_1(sK3)),
% 2.25/0.67    inference(cnf_transformation,[],[f40])).
% 2.25/0.67  fof(f820,plain,(
% 2.25/0.67    sK3 = sK4 | k1_relat_1(sK4) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(subsumption_resolution,[],[f819,f124])).
% 2.25/0.67  fof(f124,plain,(
% 2.25/0.67    v1_relat_1(sK4)),
% 2.25/0.67    inference(resolution,[],[f116,f65])).
% 2.25/0.67  fof(f819,plain,(
% 2.25/0.67    sK3 = sK4 | k1_relat_1(sK4) != k1_relat_1(sK3) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(subsumption_resolution,[],[f818,f63])).
% 2.25/0.67  fof(f63,plain,(
% 2.25/0.67    v1_funct_1(sK4)),
% 2.25/0.67    inference(cnf_transformation,[],[f40])).
% 2.25/0.67  fof(f818,plain,(
% 2.25/0.67    sK3 = sK4 | k1_relat_1(sK4) != k1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(trivial_inequality_removal,[],[f817])).
% 2.25/0.67  fof(f817,plain,(
% 2.25/0.67    k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK3,sK5(sK3,sK4)) | sK3 = sK4 | k1_relat_1(sK4) != k1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2),
% 2.25/0.67    inference(duplicate_literal_removal,[],[f816])).
% 2.25/0.67  fof(f816,plain,(
% 2.25/0.67    k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK3,sK5(sK3,sK4)) | sK3 = sK4 | k1_relat_1(sK4) != k1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2 | sK3 = sK4),
% 2.25/0.67    inference(superposition,[],[f72,f769])).
% 2.25/0.67  fof(f769,plain,(
% 2.25/0.67    k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) | k1_xboole_0 = sK2 | sK3 = sK4),
% 2.25/0.67    inference(resolution,[],[f760,f66])).
% 2.25/0.67  fof(f66,plain,(
% 2.25/0.67    ( ! [X4] : (~r2_hidden(X4,sK1) | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f40])).
% 2.25/0.67  fof(f760,plain,(
% 2.25/0.67    r2_hidden(sK5(sK3,sK4),sK1) | sK3 = sK4 | k1_xboole_0 = sK2),
% 2.25/0.67    inference(duplicate_literal_removal,[],[f759])).
% 2.25/0.67  fof(f759,plain,(
% 2.25/0.67    r2_hidden(sK5(sK3,sK4),sK1) | sK3 = sK4 | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 2.25/0.67    inference(superposition,[],[f756,f316])).
% 2.25/0.67  fof(f756,plain,(
% 2.25/0.67    r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3)) | sK3 = sK4 | k1_xboole_0 = sK2),
% 2.25/0.67    inference(subsumption_resolution,[],[f755,f316])).
% 2.25/0.67  fof(f755,plain,(
% 2.25/0.67    sK1 != k1_relat_1(sK3) | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3)) | sK3 = sK4 | k1_xboole_0 = sK2),
% 2.25/0.67    inference(superposition,[],[f754,f325])).
% 2.25/0.67  fof(f754,plain,(
% 2.25/0.67    k1_relat_1(sK4) != k1_relat_1(sK3) | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3)) | sK3 = sK4),
% 2.25/0.67    inference(subsumption_resolution,[],[f753,f124])).
% 2.25/0.67  fof(f753,plain,(
% 2.25/0.67    k1_relat_1(sK4) != k1_relat_1(sK3) | r2_hidden(sK5(sK3,sK4),k1_relat_1(sK3)) | ~v1_relat_1(sK4) | sK3 = sK4),
% 2.25/0.67    inference(resolution,[],[f400,f63])).
% 2.25/0.67  fof(f400,plain,(
% 2.25/0.67    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | r2_hidden(sK5(sK3,X0),k1_relat_1(sK3)) | ~v1_relat_1(X0) | sK3 = X0) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f398,f123])).
% 2.25/0.67  fof(f398,plain,(
% 2.25/0.67    ( ! [X0] : (r2_hidden(sK5(sK3,X0),k1_relat_1(sK3)) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK3 = X0 | ~v1_relat_1(sK3)) )),
% 2.25/0.67    inference(resolution,[],[f71,f60])).
% 2.25/0.67  fof(f71,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f42])).
% 2.25/0.67  fof(f42,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.25/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f41])).
% 2.25/0.67  fof(f41,plain,(
% 2.25/0.67    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 2.25/0.67    introduced(choice_axiom,[])).
% 2.25/0.67  fof(f24,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.25/0.67    inference(flattening,[],[f23])).
% 2.25/0.67  fof(f23,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.25/0.67    inference(ennf_transformation,[],[f11])).
% 2.25/0.67  fof(f11,axiom,(
% 2.25/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 2.32/0.67  fof(f72,plain,(
% 2.32/0.67    ( ! [X0,X1] : (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(cnf_transformation,[],[f42])).
% 2.32/0.67  fof(f67,plain,(
% 2.32/0.67    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 2.32/0.67    inference(cnf_transformation,[],[f40])).
% 2.32/0.67  fof(f65,plain,(
% 2.32/0.67    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.32/0.67    inference(cnf_transformation,[],[f40])).
% 2.32/0.67  fof(f1019,plain,(
% 2.32/0.67    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4)),
% 2.32/0.67    inference(backward_demodulation,[],[f869,f893])).
% 2.32/0.67  fof(f893,plain,(
% 2.32/0.67    k1_xboole_0 = sK3),
% 2.32/0.67    inference(resolution,[],[f885,f135])).
% 2.32/0.67  fof(f885,plain,(
% 2.32/0.67    v1_xboole_0(sK3)),
% 2.32/0.67    inference(resolution,[],[f878,f173])).
% 2.32/0.67  fof(f878,plain,(
% 2.32/0.67    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 2.32/0.67    inference(forward_demodulation,[],[f866,f102])).
% 2.32/0.67  fof(f866,plain,(
% 2.32/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 2.32/0.67    inference(backward_demodulation,[],[f62,f864])).
% 2.32/0.67  fof(f869,plain,(
% 2.32/0.67    ~r2_relset_1(sK1,k1_xboole_0,sK3,sK4)),
% 2.32/0.67    inference(backward_demodulation,[],[f67,f864])).
% 2.32/0.67  % SZS output end Proof for theBenchmark
% 2.32/0.67  % (10547)------------------------------
% 2.32/0.67  % (10547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.67  % (10547)Termination reason: Refutation
% 2.32/0.67  
% 2.32/0.67  % (10547)Memory used [KB]: 6652
% 2.32/0.67  % (10547)Time elapsed: 0.212 s
% 2.32/0.67  % (10547)------------------------------
% 2.32/0.67  % (10547)------------------------------
% 2.32/0.67  % (10539)Success in time 0.299 s
%------------------------------------------------------------------------------
