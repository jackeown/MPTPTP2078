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
% DateTime   : Thu Dec  3 13:07:49 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 401 expanded)
%              Number of leaves         :   26 ( 156 expanded)
%              Depth                    :   29
%              Number of atoms          :  534 (3213 expanded)
%              Number of equality atoms :  108 ( 742 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f596,plain,(
    $false ),
    inference(subsumption_resolution,[],[f562,f154])).

fof(f154,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f153,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK9(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
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

fof(f153,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f75,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f562,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f63,f543])).

fof(f543,plain,(
    k1_xboole_0 = sK5 ),
    inference(resolution,[],[f536,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f536,plain,(
    sP0(sK4,sK5) ),
    inference(subsumption_resolution,[],[f535,f318])).

fof(f318,plain,(
    r2_hidden(sK8,sK4) ),
    inference(subsumption_resolution,[],[f317,f71])).

fof(f71,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8))
    & k1_xboole_0 != sK4
    & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7))
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,X3,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK4
                  & r1_tarski(k2_relset_1(sK4,sK5,X3),k1_relset_1(sK5,sK3,X4))
                  & m1_subset_1(X5,sK4) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
          & v1_funct_2(X3,sK4,sK5)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,X3,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK4
                & r1_tarski(k2_relset_1(sK4,sK5,X3),k1_relset_1(sK5,sK3,X4))
                & m1_subset_1(X5,sK4) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
        & v1_funct_2(X3,sK4,sK5)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(sK6,X5))
              & k1_xboole_0 != sK4
              & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,X4))
              & m1_subset_1(X5,sK4) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(sK6,X5))
            & k1_xboole_0 != sK4
            & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,X4))
            & m1_subset_1(X5,sK4) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X5) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,X5))
          & k1_xboole_0 != sK4
          & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7))
          & m1_subset_1(X5,sK4) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X5) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,X5))
        & k1_xboole_0 != sK4
        & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7))
        & m1_subset_1(X5,sK4) )
   => ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8))
      & k1_xboole_0 != sK4
      & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7))
      & m1_subset_1(sK8,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f317,plain,
    ( k1_xboole_0 = sK4
    | r2_hidden(sK8,sK4) ),
    inference(resolution,[],[f215,f69])).

fof(f69,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | k1_xboole_0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f135,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X1),X0)
      | ~ m1_subset_1(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f79,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f535,plain,
    ( ~ r2_hidden(sK8,sK4)
    | sP0(sK4,sK5) ),
    inference(superposition,[],[f522,f272])).

fof(f272,plain,
    ( sK4 = k1_relat_1(sK6)
    | sP0(sK4,sK5) ),
    inference(subsumption_resolution,[],[f270,f65])).

fof(f65,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f270,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | sP0(sK4,sK5)
    | sK4 = k1_relat_1(sK6) ),
    inference(resolution,[],[f159,f66])).

fof(f66,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f46])).

fof(f159,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f156,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f40,f39,f38])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f156,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f96,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f522,plain,(
    ~ r2_hidden(sK8,k1_relat_1(sK6)) ),
    inference(subsumption_resolution,[],[f521,f64])).

fof(f64,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f521,plain,
    ( ~ r2_hidden(sK8,k1_relat_1(sK6))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f520,f116])).

fof(f116,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f90,f66])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f520,plain,
    ( ~ v1_relat_1(sK6)
    | ~ r2_hidden(sK8,k1_relat_1(sK6))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f509,f183])).

fof(f183,plain,(
    v5_relat_1(sK6,k1_relat_1(sK7)) ),
    inference(subsumption_resolution,[],[f181,f116])).

fof(f181,plain,
    ( v5_relat_1(sK6,k1_relat_1(sK7))
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f180,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f180,plain,(
    r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) ),
    inference(subsumption_resolution,[],[f179,f66])).

fof(f179,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f140,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f140,plain,(
    r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relat_1(sK7)) ),
    inference(subsumption_resolution,[],[f139,f68])).

fof(f68,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f139,plain,
    ( r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relat_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(superposition,[],[f70,f91])).

fof(f70,plain,(
    r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) ),
    inference(cnf_transformation,[],[f46])).

fof(f509,plain,
    ( ~ v5_relat_1(sK6,k1_relat_1(sK7))
    | ~ v1_relat_1(sK6)
    | ~ r2_hidden(sK8,k1_relat_1(sK6))
    | ~ v1_funct_1(sK6) ),
    inference(resolution,[],[f242,f309])).

fof(f309,plain,(
    ~ r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7)) ),
    inference(subsumption_resolution,[],[f237,f256])).

fof(f256,plain,(
    v5_relat_1(sK7,sK3) ),
    inference(subsumption_resolution,[],[f254,f117])).

fof(f117,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f90,f68])).

fof(f254,plain,
    ( v5_relat_1(sK7,sK3)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f253,f77])).

fof(f253,plain,(
    r1_tarski(k2_relat_1(sK7),sK3) ),
    inference(resolution,[],[f225,f87])).

fof(f225,plain,(
    m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK3)) ),
    inference(resolution,[],[f148,f68])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f93,f92])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f237,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7))
    | ~ v5_relat_1(sK7,sK3) ),
    inference(subsumption_resolution,[],[f236,f117])).

fof(f236,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7))
    | ~ v5_relat_1(sK7,sK3)
    | ~ v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f235,f67])).

fof(f67,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f235,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v5_relat_1(sK7,sK3)
    | ~ v1_relat_1(sK7) ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,
    ( k1_funct_1(sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | ~ r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v5_relat_1(sK7,sK3)
    | ~ v1_relat_1(sK7) ),
    inference(superposition,[],[f177,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f177,plain,(
    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) ),
    inference(subsumption_resolution,[],[f176,f63])).

fof(f176,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f175,f64])).

fof(f175,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f174,f65])).

fof(f174,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f173,f66])).

fof(f173,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f172,f67])).

fof(f172,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f171,f68])).

fof(f171,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f170,f69])).

fof(f170,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | ~ m1_subset_1(sK8,sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f169,f70])).

fof(f169,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | ~ r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7))
    | ~ m1_subset_1(sK8,sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f167,f71])).

fof(f167,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))
    | k1_xboole_0 = sK4
    | ~ r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7))
    | ~ m1_subset_1(sK8,sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(sK5) ),
    inference(superposition,[],[f72,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f72,plain,(
    k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) ),
    inference(cnf_transformation,[],[f46])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X1),X2)
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X1),X2)
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f125,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f125,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X6))
      | r2_hidden(X5,X7)
      | ~ v5_relat_1(X6,X7)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f82,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f63,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:22:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (10516)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.43  % (10508)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.51  % (10506)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.51  % (10505)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.53  % (10514)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.53  % (10501)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.20/0.53  % (10507)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.53  % (10523)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.53  % (10502)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (10504)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (10503)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (10517)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (10515)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.54  % (10521)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (10520)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.54  % (10526)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.54  % (10522)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.55  % (10529)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.55  % (10522)Refutation not found, incomplete strategy% (10522)------------------------------
% 1.32/0.55  % (10522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (10522)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (10522)Memory used [KB]: 1791
% 1.32/0.55  % (10522)Time elapsed: 0.141 s
% 1.32/0.55  % (10522)------------------------------
% 1.32/0.55  % (10522)------------------------------
% 1.32/0.55  % (10509)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.55  % (10513)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.55  % (10530)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.55  % (10512)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.55  % (10528)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.55  % (10511)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.55  % (10524)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.56  % (10525)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.56  % (10523)Refutation not found, incomplete strategy% (10523)------------------------------
% 1.32/0.56  % (10523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (10523)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (10523)Memory used [KB]: 11001
% 1.32/0.56  % (10523)Time elapsed: 0.137 s
% 1.32/0.56  % (10523)------------------------------
% 1.32/0.56  % (10523)------------------------------
% 1.32/0.56  % (10518)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.56  % (10519)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.57  % (10510)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.57  % (10527)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.57  % (10509)Refutation not found, incomplete strategy% (10509)------------------------------
% 1.32/0.57  % (10509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (10509)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (10509)Memory used [KB]: 11129
% 1.32/0.57  % (10509)Time elapsed: 0.161 s
% 1.32/0.57  % (10509)------------------------------
% 1.32/0.57  % (10509)------------------------------
% 1.32/0.58  % (10530)Refutation found. Thanks to Tanya!
% 1.32/0.58  % SZS status Theorem for theBenchmark
% 1.32/0.58  % SZS output start Proof for theBenchmark
% 1.32/0.58  fof(f596,plain,(
% 1.32/0.58    $false),
% 1.32/0.58    inference(subsumption_resolution,[],[f562,f154])).
% 1.32/0.58  fof(f154,plain,(
% 1.32/0.58    v1_xboole_0(k1_xboole_0)),
% 1.32/0.58    inference(resolution,[],[f153,f74])).
% 1.32/0.58  fof(f74,plain,(
% 1.32/0.58    ( ! [X0] : (r2_hidden(sK9(X0),X0) | v1_xboole_0(X0)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f50])).
% 1.32/0.58  fof(f50,plain,(
% 1.32/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK9(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).
% 1.32/0.58  fof(f49,plain,(
% 1.32/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 1.32/0.58    introduced(choice_axiom,[])).
% 1.32/0.58  fof(f48,plain,(
% 1.32/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.58    inference(rectify,[],[f47])).
% 1.32/0.58  fof(f47,plain,(
% 1.32/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.58    inference(nnf_transformation,[],[f1])).
% 1.32/0.58  fof(f1,axiom,(
% 1.32/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.32/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.32/0.58  fof(f153,plain,(
% 1.32/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.58    inference(equality_resolution,[],[f122])).
% 1.32/0.58  fof(f122,plain,(
% 1.32/0.58    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~r2_hidden(X0,X1)) )),
% 1.32/0.58    inference(superposition,[],[f75,f78])).
% 1.32/0.58  fof(f78,plain,(
% 1.32/0.58    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f22])).
% 1.32/0.58  fof(f22,plain,(
% 1.32/0.58    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.32/0.58    inference(ennf_transformation,[],[f4])).
% 1.32/0.58  fof(f4,axiom,(
% 1.32/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.32/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.32/0.58  fof(f75,plain,(
% 1.32/0.58    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 1.32/0.58    inference(cnf_transformation,[],[f5])).
% 1.32/0.58  fof(f5,axiom,(
% 1.32/0.58    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 1.32/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.32/0.58  fof(f562,plain,(
% 1.32/0.58    ~v1_xboole_0(k1_xboole_0)),
% 1.32/0.58    inference(backward_demodulation,[],[f63,f543])).
% 1.32/0.58  fof(f543,plain,(
% 1.32/0.58    k1_xboole_0 = sK5),
% 1.32/0.58    inference(resolution,[],[f536,f98])).
% 1.32/0.58  fof(f98,plain,(
% 1.32/0.58    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 1.32/0.58    inference(cnf_transformation,[],[f62])).
% 1.32/0.58  fof(f62,plain,(
% 1.32/0.58    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.32/0.58    inference(nnf_transformation,[],[f38])).
% 1.32/0.58  fof(f38,plain,(
% 1.32/0.58    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.32/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.32/0.58  fof(f536,plain,(
% 1.32/0.58    sP0(sK4,sK5)),
% 1.32/0.58    inference(subsumption_resolution,[],[f535,f318])).
% 1.32/0.58  fof(f318,plain,(
% 1.32/0.58    r2_hidden(sK8,sK4)),
% 1.32/0.58    inference(subsumption_resolution,[],[f317,f71])).
% 1.32/0.58  fof(f71,plain,(
% 1.32/0.58    k1_xboole_0 != sK4),
% 1.32/0.58    inference(cnf_transformation,[],[f46])).
% 1.32/0.58  fof(f46,plain,(
% 1.32/0.58    (((k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)) & ~v1_xboole_0(sK5)),
% 1.32/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f45,f44,f43,f42])).
% 1.32/0.58  fof(f42,plain,(
% 1.32/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK4,sK5,sK3,X3,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,X3),k1_relset_1(sK5,sK3,X4)) & m1_subset_1(X5,sK4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X3,sK4,sK5) & v1_funct_1(X3)) & ~v1_xboole_0(sK5))),
% 1.32/0.58    introduced(choice_axiom,[])).
% 1.32/0.58  fof(f43,plain,(
% 1.32/0.58    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK4,sK5,sK3,X3,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,X3),k1_relset_1(sK5,sK3,X4)) & m1_subset_1(X5,sK4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X3,sK4,sK5) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(sK6,X5)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,X4)) & m1_subset_1(X5,sK4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_1(X4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 1.32/0.58    introduced(choice_axiom,[])).
% 1.32/0.58  fof(f44,plain,(
% 1.32/0.58    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(sK6,X5)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,X4)) & m1_subset_1(X5,sK4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X5) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,X5)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) & m1_subset_1(X5,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_1(sK7))),
% 1.32/0.58    introduced(choice_axiom,[])).
% 1.32/0.58  fof(f45,plain,(
% 1.32/0.58    ? [X5] : (k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X5) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,X5)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) & m1_subset_1(X5,sK4)) => (k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) & m1_subset_1(sK8,sK4))),
% 1.32/0.58    introduced(choice_axiom,[])).
% 1.32/0.58  fof(f20,plain,(
% 1.32/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.32/0.58    inference(flattening,[],[f19])).
% 1.32/0.58  fof(f19,plain,(
% 1.32/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.32/0.58    inference(ennf_transformation,[],[f18])).
% 1.32/0.58  fof(f18,negated_conjecture,(
% 1.32/0.58    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.32/0.58    inference(negated_conjecture,[],[f17])).
% 1.32/0.58  fof(f17,conjecture,(
% 1.32/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.32/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 1.32/0.58  fof(f317,plain,(
% 1.32/0.58    k1_xboole_0 = sK4 | r2_hidden(sK8,sK4)),
% 1.32/0.58    inference(resolution,[],[f215,f69])).
% 1.32/0.58  fof(f69,plain,(
% 1.32/0.58    m1_subset_1(sK8,sK4)),
% 1.32/0.58    inference(cnf_transformation,[],[f46])).
% 1.32/0.58  fof(f215,plain,(
% 1.32/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | k1_xboole_0 = X1 | r2_hidden(X0,X1)) )),
% 1.32/0.58    inference(resolution,[],[f135,f85])).
% 1.32/0.58  fof(f85,plain,(
% 1.32/0.58    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f56])).
% 1.32/0.58  fof(f56,plain,(
% 1.32/0.58    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.32/0.58    inference(nnf_transformation,[],[f3])).
% 1.32/0.58  fof(f3,axiom,(
% 1.32/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.32/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.32/0.58  fof(f135,plain,(
% 1.32/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X1),X0) | ~m1_subset_1(X1,X0) | k1_xboole_0 = X0) )),
% 1.32/0.58    inference(resolution,[],[f79,f87])).
% 1.32/0.59  fof(f87,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f57])).
% 1.32/0.59  fof(f57,plain,(
% 1.32/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.32/0.59    inference(nnf_transformation,[],[f7])).
% 1.32/0.59  fof(f7,axiom,(
% 1.32/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.32/0.59  fof(f79,plain,(
% 1.32/0.59    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f24])).
% 1.32/0.59  fof(f24,plain,(
% 1.32/0.59    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 1.32/0.59    inference(flattening,[],[f23])).
% 1.32/0.59  fof(f23,plain,(
% 1.32/0.59    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 1.32/0.59    inference(ennf_transformation,[],[f6])).
% 1.32/0.59  fof(f6,axiom,(
% 1.32/0.59    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 1.32/0.59  fof(f535,plain,(
% 1.32/0.59    ~r2_hidden(sK8,sK4) | sP0(sK4,sK5)),
% 1.32/0.59    inference(superposition,[],[f522,f272])).
% 1.32/0.59  fof(f272,plain,(
% 1.32/0.59    sK4 = k1_relat_1(sK6) | sP0(sK4,sK5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f270,f65])).
% 1.32/0.59  fof(f65,plain,(
% 1.32/0.59    v1_funct_2(sK6,sK4,sK5)),
% 1.32/0.59    inference(cnf_transformation,[],[f46])).
% 1.32/0.59  fof(f270,plain,(
% 1.32/0.59    ~v1_funct_2(sK6,sK4,sK5) | sP0(sK4,sK5) | sK4 = k1_relat_1(sK6)),
% 1.32/0.59    inference(resolution,[],[f159,f66])).
% 1.32/0.59  fof(f66,plain,(
% 1.32/0.59    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.32/0.59    inference(cnf_transformation,[],[f46])).
% 1.32/0.59  fof(f159,plain,(
% 1.32/0.59    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.32/0.59    inference(subsumption_resolution,[],[f156,f100])).
% 1.32/0.59  fof(f100,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f41])).
% 1.32/0.59  fof(f41,plain,(
% 1.32/0.59    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.59    inference(definition_folding,[],[f37,f40,f39,f38])).
% 1.32/0.59  fof(f39,plain,(
% 1.32/0.59    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.32/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.32/0.59  fof(f40,plain,(
% 1.32/0.59    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.32/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.32/0.59  fof(f37,plain,(
% 1.32/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.59    inference(flattening,[],[f36])).
% 1.32/0.59  fof(f36,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.59    inference(ennf_transformation,[],[f14])).
% 1.32/0.59  fof(f14,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.32/0.59  fof(f156,plain,(
% 1.32/0.59    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.32/0.59    inference(superposition,[],[f96,f91])).
% 1.32/0.59  fof(f91,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.59    inference(cnf_transformation,[],[f33])).
% 1.32/0.59  fof(f33,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.59    inference(ennf_transformation,[],[f12])).
% 1.32/0.59  fof(f12,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.32/0.59  fof(f96,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f61])).
% 1.32/0.59  fof(f61,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 1.32/0.59    inference(rectify,[],[f60])).
% 1.32/0.59  fof(f60,plain,(
% 1.32/0.59    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.32/0.59    inference(nnf_transformation,[],[f39])).
% 1.32/0.59  fof(f522,plain,(
% 1.32/0.59    ~r2_hidden(sK8,k1_relat_1(sK6))),
% 1.32/0.59    inference(subsumption_resolution,[],[f521,f64])).
% 1.32/0.59  fof(f64,plain,(
% 1.32/0.59    v1_funct_1(sK6)),
% 1.32/0.59    inference(cnf_transformation,[],[f46])).
% 1.32/0.59  fof(f521,plain,(
% 1.32/0.59    ~r2_hidden(sK8,k1_relat_1(sK6)) | ~v1_funct_1(sK6)),
% 1.32/0.59    inference(subsumption_resolution,[],[f520,f116])).
% 1.32/0.59  fof(f116,plain,(
% 1.32/0.59    v1_relat_1(sK6)),
% 1.32/0.59    inference(resolution,[],[f90,f66])).
% 1.32/0.59  fof(f90,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f32])).
% 1.32/0.59  fof(f32,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.59    inference(ennf_transformation,[],[f10])).
% 1.32/0.59  fof(f10,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.32/0.59  fof(f520,plain,(
% 1.32/0.59    ~v1_relat_1(sK6) | ~r2_hidden(sK8,k1_relat_1(sK6)) | ~v1_funct_1(sK6)),
% 1.32/0.59    inference(subsumption_resolution,[],[f509,f183])).
% 1.32/0.59  fof(f183,plain,(
% 1.32/0.59    v5_relat_1(sK6,k1_relat_1(sK7))),
% 1.32/0.59    inference(subsumption_resolution,[],[f181,f116])).
% 1.32/0.59  fof(f181,plain,(
% 1.32/0.59    v5_relat_1(sK6,k1_relat_1(sK7)) | ~v1_relat_1(sK6)),
% 1.32/0.59    inference(resolution,[],[f180,f77])).
% 1.32/0.59  fof(f77,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f51])).
% 1.32/0.59  fof(f51,plain,(
% 1.32/0.59    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.32/0.59    inference(nnf_transformation,[],[f21])).
% 1.32/0.59  fof(f21,plain,(
% 1.32/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.32/0.59    inference(ennf_transformation,[],[f8])).
% 1.32/0.59  fof(f8,axiom,(
% 1.32/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.32/0.59  fof(f180,plain,(
% 1.32/0.59    r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))),
% 1.32/0.59    inference(subsumption_resolution,[],[f179,f66])).
% 1.32/0.59  fof(f179,plain,(
% 1.32/0.59    r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.32/0.59    inference(superposition,[],[f140,f92])).
% 1.32/0.59  fof(f92,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.59    inference(cnf_transformation,[],[f34])).
% 1.32/0.59  fof(f34,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.59    inference(ennf_transformation,[],[f13])).
% 1.32/0.59  fof(f13,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.32/0.59  fof(f140,plain,(
% 1.32/0.59    r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relat_1(sK7))),
% 1.32/0.59    inference(subsumption_resolution,[],[f139,f68])).
% 1.32/0.59  fof(f68,plain,(
% 1.32/0.59    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 1.32/0.59    inference(cnf_transformation,[],[f46])).
% 1.32/0.59  fof(f139,plain,(
% 1.32/0.59    r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relat_1(sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 1.32/0.59    inference(superposition,[],[f70,f91])).
% 1.32/0.59  fof(f70,plain,(
% 1.32/0.59    r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7))),
% 1.32/0.59    inference(cnf_transformation,[],[f46])).
% 1.32/0.59  fof(f509,plain,(
% 1.32/0.59    ~v5_relat_1(sK6,k1_relat_1(sK7)) | ~v1_relat_1(sK6) | ~r2_hidden(sK8,k1_relat_1(sK6)) | ~v1_funct_1(sK6)),
% 1.32/0.59    inference(resolution,[],[f242,f309])).
% 1.32/0.59  fof(f309,plain,(
% 1.32/0.59    ~r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7))),
% 1.32/0.59    inference(subsumption_resolution,[],[f237,f256])).
% 1.32/0.59  fof(f256,plain,(
% 1.32/0.59    v5_relat_1(sK7,sK3)),
% 1.32/0.59    inference(subsumption_resolution,[],[f254,f117])).
% 1.32/0.59  fof(f117,plain,(
% 1.32/0.59    v1_relat_1(sK7)),
% 1.32/0.59    inference(resolution,[],[f90,f68])).
% 1.32/0.59  fof(f254,plain,(
% 1.32/0.59    v5_relat_1(sK7,sK3) | ~v1_relat_1(sK7)),
% 1.32/0.59    inference(resolution,[],[f253,f77])).
% 1.32/0.59  fof(f253,plain,(
% 1.32/0.59    r1_tarski(k2_relat_1(sK7),sK3)),
% 1.32/0.59    inference(resolution,[],[f225,f87])).
% 1.32/0.59  fof(f225,plain,(
% 1.32/0.59    m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK3))),
% 1.32/0.59    inference(resolution,[],[f148,f68])).
% 1.32/0.59  fof(f148,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 1.32/0.59    inference(duplicate_literal_removal,[],[f147])).
% 1.32/0.59  fof(f147,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.59    inference(superposition,[],[f93,f92])).
% 1.32/0.59  fof(f93,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.59    inference(cnf_transformation,[],[f35])).
% 1.32/0.59  fof(f35,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.59    inference(ennf_transformation,[],[f11])).
% 1.32/0.59  fof(f11,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.32/0.59  fof(f237,plain,(
% 1.32/0.59    ~r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7)) | ~v5_relat_1(sK7,sK3)),
% 1.32/0.59    inference(subsumption_resolution,[],[f236,f117])).
% 1.32/0.59  fof(f236,plain,(
% 1.32/0.59    ~r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7)) | ~v5_relat_1(sK7,sK3) | ~v1_relat_1(sK7)),
% 1.32/0.59    inference(subsumption_resolution,[],[f235,f67])).
% 1.32/0.59  fof(f67,plain,(
% 1.32/0.59    v1_funct_1(sK7)),
% 1.32/0.59    inference(cnf_transformation,[],[f46])).
% 1.32/0.59  fof(f235,plain,(
% 1.32/0.59    ~r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v5_relat_1(sK7,sK3) | ~v1_relat_1(sK7)),
% 1.32/0.59    inference(trivial_inequality_removal,[],[f234])).
% 1.32/0.59  fof(f234,plain,(
% 1.32/0.59    k1_funct_1(sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | ~r2_hidden(k1_funct_1(sK6,sK8),k1_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v5_relat_1(sK7,sK3) | ~v1_relat_1(sK7)),
% 1.32/0.59    inference(superposition,[],[f177,f81])).
% 1.32/0.59  fof(f81,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f28])).
% 1.32/0.59  fof(f28,plain,(
% 1.32/0.59    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.32/0.59    inference(flattening,[],[f27])).
% 1.32/0.59  fof(f27,plain,(
% 1.32/0.59    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.32/0.59    inference(ennf_transformation,[],[f15])).
% 1.32/0.59  fof(f15,axiom,(
% 1.32/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 1.32/0.59  fof(f177,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8))),
% 1.32/0.59    inference(subsumption_resolution,[],[f176,f63])).
% 1.32/0.59  fof(f176,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | v1_xboole_0(sK5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f175,f64])).
% 1.32/0.59  fof(f175,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | ~v1_funct_1(sK6) | v1_xboole_0(sK5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f174,f65])).
% 1.32/0.59  fof(f174,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f173,f66])).
% 1.32/0.59  fof(f173,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f172,f67])).
% 1.32/0.59  fof(f172,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f171,f68])).
% 1.32/0.59  fof(f171,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f170,f69])).
% 1.32/0.59  fof(f170,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | ~m1_subset_1(sK8,sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f169,f70])).
% 1.32/0.59  fof(f169,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | ~r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) | ~m1_subset_1(sK8,sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f167,f71])).
% 1.32/0.59  fof(f167,plain,(
% 1.32/0.59    k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) | k1_xboole_0 = sK4 | ~r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) | ~m1_subset_1(sK8,sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6) | v1_xboole_0(sK5)),
% 1.32/0.59    inference(superposition,[],[f72,f89])).
% 1.32/0.59  fof(f89,plain,(
% 1.32/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f31])).
% 1.32/0.59  fof(f31,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 1.32/0.59    inference(flattening,[],[f30])).
% 1.32/0.59  fof(f30,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 1.32/0.59    inference(ennf_transformation,[],[f16])).
% 1.32/0.59  fof(f16,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 1.32/0.59  fof(f72,plain,(
% 1.32/0.59    k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8))),
% 1.32/0.59    inference(cnf_transformation,[],[f46])).
% 1.32/0.59  fof(f242,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X0,X1),X2) | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0)) )),
% 1.32/0.59    inference(duplicate_literal_removal,[],[f239])).
% 1.32/0.59  fof(f239,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X0,X1),X2) | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(resolution,[],[f125,f80])).
% 1.32/0.59  fof(f80,plain,(
% 1.32/0.59    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f26])).
% 1.32/0.59  fof(f26,plain,(
% 1.32/0.59    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.59    inference(flattening,[],[f25])).
% 1.32/0.59  fof(f25,plain,(
% 1.32/0.59    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.32/0.59    inference(ennf_transformation,[],[f9])).
% 1.32/0.59  fof(f9,axiom,(
% 1.32/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 1.32/0.59  fof(f125,plain,(
% 1.32/0.59    ( ! [X6,X7,X5] : (~r2_hidden(X5,k2_relat_1(X6)) | r2_hidden(X5,X7) | ~v5_relat_1(X6,X7) | ~v1_relat_1(X6)) )),
% 1.32/0.59    inference(resolution,[],[f82,f76])).
% 1.32/0.59  fof(f76,plain,(
% 1.32/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f51])).
% 1.32/0.59  fof(f82,plain,(
% 1.32/0.59    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f55])).
% 1.32/0.59  fof(f55,plain,(
% 1.32/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f53,f54])).
% 1.32/0.59  fof(f54,plain,(
% 1.32/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 1.32/0.59    introduced(choice_axiom,[])).
% 1.32/0.59  fof(f53,plain,(
% 1.32/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.59    inference(rectify,[],[f52])).
% 1.32/0.59  fof(f52,plain,(
% 1.32/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.59    inference(nnf_transformation,[],[f29])).
% 1.32/0.59  fof(f29,plain,(
% 1.32/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.32/0.59    inference(ennf_transformation,[],[f2])).
% 1.32/0.59  fof(f2,axiom,(
% 1.32/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.32/0.59  fof(f63,plain,(
% 1.32/0.59    ~v1_xboole_0(sK5)),
% 1.32/0.59    inference(cnf_transformation,[],[f46])).
% 1.32/0.59  % SZS output end Proof for theBenchmark
% 1.32/0.59  % (10530)------------------------------
% 1.32/0.59  % (10530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.59  % (10530)Termination reason: Refutation
% 1.32/0.59  
% 1.32/0.59  % (10530)Memory used [KB]: 2174
% 1.32/0.59  % (10530)Time elapsed: 0.187 s
% 1.32/0.59  % (10530)------------------------------
% 1.32/0.59  % (10530)------------------------------
% 1.32/0.59  % (10497)Success in time 0.225 s
%------------------------------------------------------------------------------
