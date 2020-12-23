%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:54 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 374 expanded)
%              Number of leaves         :   28 (  96 expanded)
%              Depth                    :   22
%              Number of atoms          :  340 (1307 expanded)
%              Number of equality atoms :  106 ( 330 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(subsumption_resolution,[],[f140,f408])).

fof(f408,plain,(
    ! [X0] : ~ r2_hidden(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f407,f402])).

fof(f402,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f388,f76])).

fof(f76,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f388,plain,(
    k3_tarski(k1_xboole_0) = sK1 ),
    inference(superposition,[],[f82,f386])).

fof(f386,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f383,f74])).

fof(f74,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f58])).

fof(f58,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f383,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f381,f273])).

fof(f273,plain,(
    v1_funct_2(k1_xboole_0,k1_tarski(sK1),sK2) ),
    inference(backward_demodulation,[],[f72,f271])).

fof(f271,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f266,f269])).

fof(f269,plain,(
    ~ r2_hidden(sK1,k1_relat_1(sK3)) ),
    inference(resolution,[],[f268,f259])).

fof(f259,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f258])).

fof(f258,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k1_tarski(k1_funct_1(sK3,sK1))
    | ~ r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3)) ),
    inference(superposition,[],[f101,f253])).

fof(f253,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) = k4_xboole_0(k1_tarski(k1_funct_1(sK3,sK1)),k2_relat_1(sK3)) ),
    inference(resolution,[],[f227,f75])).

fof(f75,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f227,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK2)
      | k1_tarski(X2) = k4_xboole_0(k1_tarski(X2),k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f102,f181])).

fof(f181,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f174,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f64,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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

fof(f174,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f173,f145])).

fof(f145,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f104,f73])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f173,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f172,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f172,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f106,f73])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f268,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f267,f145])).

fof(f267,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f97,f71])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f266,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f264,f87])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f264,plain,
    ( ~ r2_hidden(sK4(sK3),sK3)
    | r2_hidden(sK1,k1_relat_1(sK3))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f238,f145])).

fof(f238,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(sK4(sK3),X0)
      | r2_hidden(sK1,k1_relat_1(X0))
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f85,f236])).

fof(f236,plain,
    ( sK1 = k1_mcart_1(sK4(sK3))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f231,f87])).

fof(f231,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | k1_mcart_1(X0) = sK1 ) ),
    inference(resolution,[],[f114,f217])).

fof(f217,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_zfmisc_1(k1_tarski(sK1),sK2))
      | ~ r2_hidden(X2,sK3) ) ),
    inference(resolution,[],[f96,f73])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

fof(f72,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f381,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f379,f263])).

fof(f263,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f261,f77])).

fof(f77,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f261,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f105,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f379,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f107,f229])).

fof(f229,plain,(
    ! [X0,X1] : sP0(X0,k1_xboole_0,X1) ),
    inference(resolution,[],[f111,f80])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
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

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f82,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f407,plain,(
    ! [X0] : ~ r2_hidden(sK1,X0) ),
    inference(subsumption_resolution,[],[f389,f167])).

fof(f167,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f163,f83])).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f163,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f92,f151])).

fof(f151,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f149,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f149,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f136,f90])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f136,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f90,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f389,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f101,f386])).

fof(f140,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f138,f79])).

fof(f79,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f138,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f95,f80])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.51  % (15605)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (15612)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (15611)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (15617)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (15615)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (15609)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (15604)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (15631)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (15623)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (15608)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (15628)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (15613)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (15613)Refutation not found, incomplete strategy% (15613)------------------------------
% 0.22/0.56  % (15613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15613)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15613)Memory used [KB]: 10618
% 0.22/0.56  % (15613)Time elapsed: 0.147 s
% 0.22/0.56  % (15613)------------------------------
% 0.22/0.56  % (15613)------------------------------
% 0.22/0.56  % (15603)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (15632)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (15620)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (15629)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (15627)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (15607)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (15625)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (15624)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.57  % (15606)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.57  % (15616)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.69/0.58  % (15621)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.69/0.58  % (15620)Refutation not found, incomplete strategy% (15620)------------------------------
% 1.69/0.58  % (15620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (15620)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (15620)Memory used [KB]: 10618
% 1.69/0.58  % (15620)Time elapsed: 0.174 s
% 1.69/0.58  % (15620)------------------------------
% 1.69/0.58  % (15620)------------------------------
% 1.69/0.58  % (15618)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.69/0.59  % (15630)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.69/0.59  % (15626)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.81/0.60  % (15622)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.81/0.60  % (15614)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.81/0.60  % (15610)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.81/0.62  % (15619)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.10/0.63  % (15629)Refutation not found, incomplete strategy% (15629)------------------------------
% 2.10/0.63  % (15629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.63  % (15629)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.63  
% 2.10/0.63  % (15629)Memory used [KB]: 11001
% 2.10/0.63  % (15629)Time elapsed: 0.231 s
% 2.10/0.63  % (15629)------------------------------
% 2.10/0.63  % (15629)------------------------------
% 2.10/0.63  % (15610)Refutation found. Thanks to Tanya!
% 2.10/0.63  % SZS status Theorem for theBenchmark
% 2.10/0.63  % SZS output start Proof for theBenchmark
% 2.10/0.63  fof(f409,plain,(
% 2.10/0.63    $false),
% 2.10/0.63    inference(subsumption_resolution,[],[f140,f408])).
% 2.10/0.63  fof(f408,plain,(
% 2.10/0.63    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0)) )),
% 2.10/0.63    inference(forward_demodulation,[],[f407,f402])).
% 2.10/0.63  fof(f402,plain,(
% 2.10/0.63    k1_xboole_0 = sK1),
% 2.10/0.63    inference(forward_demodulation,[],[f388,f76])).
% 2.10/0.63  fof(f76,plain,(
% 2.10/0.63    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 2.10/0.63    inference(cnf_transformation,[],[f15])).
% 2.10/0.63  fof(f15,axiom,(
% 2.10/0.63    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 2.10/0.63  fof(f388,plain,(
% 2.10/0.63    k3_tarski(k1_xboole_0) = sK1),
% 2.10/0.63    inference(superposition,[],[f82,f386])).
% 2.10/0.63  fof(f386,plain,(
% 2.10/0.63    k1_xboole_0 = k1_tarski(sK1)),
% 2.10/0.63    inference(subsumption_resolution,[],[f383,f74])).
% 2.10/0.63  fof(f74,plain,(
% 2.10/0.63    k1_xboole_0 != sK2),
% 2.10/0.63    inference(cnf_transformation,[],[f59])).
% 2.10/0.63  fof(f59,plain,(
% 2.10/0.63    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 2.10/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f58])).
% 2.10/0.63  fof(f58,plain,(
% 2.10/0.63    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f38,plain,(
% 2.10/0.63    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.10/0.63    inference(flattening,[],[f37])).
% 2.10/0.63  fof(f37,plain,(
% 2.10/0.63    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.10/0.63    inference(ennf_transformation,[],[f34])).
% 2.10/0.63  fof(f34,negated_conjecture,(
% 2.10/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.10/0.63    inference(negated_conjecture,[],[f33])).
% 2.10/0.63  fof(f33,conjecture,(
% 2.10/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 2.10/0.63  fof(f383,plain,(
% 2.10/0.63    k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = sK2),
% 2.10/0.63    inference(resolution,[],[f381,f273])).
% 2.10/0.63  fof(f273,plain,(
% 2.10/0.63    v1_funct_2(k1_xboole_0,k1_tarski(sK1),sK2)),
% 2.10/0.63    inference(backward_demodulation,[],[f72,f271])).
% 2.10/0.63  fof(f271,plain,(
% 2.10/0.63    k1_xboole_0 = sK3),
% 2.10/0.63    inference(subsumption_resolution,[],[f266,f269])).
% 2.10/0.63  fof(f269,plain,(
% 2.10/0.63    ~r2_hidden(sK1,k1_relat_1(sK3))),
% 2.10/0.63    inference(resolution,[],[f268,f259])).
% 2.10/0.63  fof(f259,plain,(
% 2.10/0.63    ~r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3))),
% 2.10/0.63    inference(trivial_inequality_removal,[],[f258])).
% 2.10/0.63  fof(f258,plain,(
% 2.10/0.63    k1_tarski(k1_funct_1(sK3,sK1)) != k1_tarski(k1_funct_1(sK3,sK1)) | ~r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(sK3))),
% 2.10/0.63    inference(superposition,[],[f101,f253])).
% 2.10/0.63  fof(f253,plain,(
% 2.10/0.63    k1_tarski(k1_funct_1(sK3,sK1)) = k4_xboole_0(k1_tarski(k1_funct_1(sK3,sK1)),k2_relat_1(sK3))),
% 2.10/0.63    inference(resolution,[],[f227,f75])).
% 2.10/0.63  fof(f75,plain,(
% 2.10/0.63    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 2.10/0.63    inference(cnf_transformation,[],[f59])).
% 2.10/0.63  fof(f227,plain,(
% 2.10/0.63    ( ! [X2] : (r2_hidden(X2,sK2) | k1_tarski(X2) = k4_xboole_0(k1_tarski(X2),k2_relat_1(sK3))) )),
% 2.10/0.63    inference(resolution,[],[f102,f181])).
% 2.10/0.63  fof(f181,plain,(
% 2.10/0.63    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X0,sK2)) )),
% 2.10/0.63    inference(resolution,[],[f174,f98])).
% 2.10/0.63  fof(f98,plain,(
% 2.10/0.63    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f66])).
% 2.10/0.63  fof(f66,plain,(
% 2.10/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.10/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f64,f65])).
% 2.10/0.63  fof(f65,plain,(
% 2.10/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f64,plain,(
% 2.10/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.10/0.63    inference(rectify,[],[f63])).
% 2.10/0.63  fof(f63,plain,(
% 2.10/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.10/0.63    inference(nnf_transformation,[],[f47])).
% 2.10/0.63  fof(f47,plain,(
% 2.10/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f2])).
% 2.10/0.63  fof(f2,axiom,(
% 2.10/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.10/0.63  fof(f174,plain,(
% 2.10/0.63    r1_tarski(k2_relat_1(sK3),sK2)),
% 2.10/0.63    inference(subsumption_resolution,[],[f173,f145])).
% 2.10/0.63  fof(f145,plain,(
% 2.10/0.63    v1_relat_1(sK3)),
% 2.10/0.63    inference(resolution,[],[f104,f73])).
% 2.10/0.63  fof(f73,plain,(
% 2.10/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.10/0.63    inference(cnf_transformation,[],[f59])).
% 2.10/0.63  fof(f104,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f48])).
% 2.10/0.63  fof(f48,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(ennf_transformation,[],[f26])).
% 2.10/0.63  fof(f26,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.10/0.63  fof(f173,plain,(
% 2.10/0.63    r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 2.10/0.63    inference(resolution,[],[f172,f93])).
% 2.10/0.63  fof(f93,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f62])).
% 2.10/0.63  fof(f62,plain,(
% 2.10/0.63    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(nnf_transformation,[],[f41])).
% 2.10/0.63  fof(f41,plain,(
% 2.10/0.63    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(ennf_transformation,[],[f23])).
% 2.10/0.63  fof(f23,axiom,(
% 2.10/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.10/0.63  fof(f172,plain,(
% 2.10/0.63    v5_relat_1(sK3,sK2)),
% 2.10/0.63    inference(resolution,[],[f106,f73])).
% 2.10/0.63  fof(f106,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f50])).
% 2.10/0.63  fof(f50,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(ennf_transformation,[],[f36])).
% 2.10/0.63  fof(f36,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.10/0.63    inference(pure_predicate_removal,[],[f27])).
% 2.10/0.63  fof(f27,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.10/0.63  fof(f102,plain,(
% 2.10/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f67])).
% 2.10/0.63  fof(f67,plain,(
% 2.10/0.63    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 2.10/0.63    inference(nnf_transformation,[],[f14])).
% 2.10/0.63  fof(f14,axiom,(
% 2.10/0.63    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 2.10/0.63  fof(f101,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f67])).
% 2.10/0.63  fof(f268,plain,(
% 2.10/0.63    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 2.10/0.63    inference(subsumption_resolution,[],[f267,f145])).
% 2.10/0.63  fof(f267,plain,(
% 2.10/0.63    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 2.10/0.63    inference(resolution,[],[f97,f71])).
% 2.10/0.63  fof(f71,plain,(
% 2.10/0.63    v1_funct_1(sK3)),
% 2.10/0.63    inference(cnf_transformation,[],[f59])).
% 2.10/0.63  fof(f97,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f46])).
% 2.10/0.63  fof(f46,plain,(
% 2.10/0.63    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(flattening,[],[f45])).
% 2.10/0.63  fof(f45,plain,(
% 2.10/0.63    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.10/0.63    inference(ennf_transformation,[],[f25])).
% 2.10/0.63  fof(f25,axiom,(
% 2.10/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 2.10/0.63  fof(f266,plain,(
% 2.10/0.63    r2_hidden(sK1,k1_relat_1(sK3)) | k1_xboole_0 = sK3),
% 2.10/0.63    inference(subsumption_resolution,[],[f264,f87])).
% 2.10/0.63  fof(f87,plain,(
% 2.10/0.63    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 2.10/0.63    inference(cnf_transformation,[],[f61])).
% 2.10/0.63  fof(f61,plain,(
% 2.10/0.63    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 2.10/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f60])).
% 2.10/0.63  fof(f60,plain,(
% 2.10/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f40,plain,(
% 2.10/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.10/0.63    inference(ennf_transformation,[],[f35])).
% 2.10/0.63  fof(f35,plain,(
% 2.10/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.10/0.63    inference(pure_predicate_removal,[],[f30])).
% 2.10/0.63  fof(f30,axiom,(
% 2.10/0.63    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 2.10/0.63  fof(f264,plain,(
% 2.10/0.63    ~r2_hidden(sK4(sK3),sK3) | r2_hidden(sK1,k1_relat_1(sK3)) | k1_xboole_0 = sK3),
% 2.10/0.63    inference(resolution,[],[f238,f145])).
% 2.10/0.63  fof(f238,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~r2_hidden(sK4(sK3),X0) | r2_hidden(sK1,k1_relat_1(X0)) | k1_xboole_0 = sK3) )),
% 2.10/0.63    inference(superposition,[],[f85,f236])).
% 2.10/0.63  fof(f236,plain,(
% 2.10/0.63    sK1 = k1_mcart_1(sK4(sK3)) | k1_xboole_0 = sK3),
% 2.10/0.63    inference(resolution,[],[f231,f87])).
% 2.10/0.63  fof(f231,plain,(
% 2.10/0.63    ( ! [X0] : (~r2_hidden(X0,sK3) | k1_mcart_1(X0) = sK1) )),
% 2.10/0.63    inference(resolution,[],[f114,f217])).
% 2.10/0.63  fof(f217,plain,(
% 2.10/0.63    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(k1_tarski(sK1),sK2)) | ~r2_hidden(X2,sK3)) )),
% 2.10/0.63    inference(resolution,[],[f96,f73])).
% 2.10/0.63  fof(f96,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f44])).
% 2.10/0.63  fof(f44,plain,(
% 2.10/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f18])).
% 2.10/0.63  fof(f18,axiom,(
% 2.10/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.10/0.63  fof(f114,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f53,plain,(
% 2.10/0.63    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 2.10/0.63    inference(ennf_transformation,[],[f29])).
% 2.10/0.63  fof(f29,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 2.10/0.63  fof(f85,plain,(
% 2.10/0.63    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) | ~r2_hidden(X1,X0) | ~v1_relat_1(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f39])).
% 2.10/0.63  fof(f39,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : ((r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f31])).
% 2.10/0.63  fof(f31,axiom,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).
% 2.10/0.63  fof(f72,plain,(
% 2.10/0.63    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 2.10/0.63    inference(cnf_transformation,[],[f59])).
% 2.10/0.63  fof(f381,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 2.10/0.63    inference(forward_demodulation,[],[f379,f263])).
% 2.10/0.63  fof(f263,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 2.10/0.63    inference(forward_demodulation,[],[f261,f77])).
% 2.10/0.63  fof(f77,plain,(
% 2.10/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.10/0.63    inference(cnf_transformation,[],[f24])).
% 2.10/0.63  fof(f24,axiom,(
% 2.10/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 2.10/0.63  fof(f261,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 2.10/0.63    inference(resolution,[],[f105,f80])).
% 2.10/0.63  fof(f80,plain,(
% 2.10/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f19,axiom,(
% 2.10/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.10/0.63  fof(f105,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f49])).
% 2.10/0.63  fof(f49,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(ennf_transformation,[],[f28])).
% 2.10/0.63  fof(f28,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.10/0.63  fof(f379,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,k1_xboole_0) = X0) )),
% 2.10/0.63    inference(resolution,[],[f107,f229])).
% 2.10/0.63  fof(f229,plain,(
% 2.10/0.63    ( ! [X0,X1] : (sP0(X0,k1_xboole_0,X1)) )),
% 2.10/0.63    inference(resolution,[],[f111,f80])).
% 2.10/0.63  fof(f111,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f70])).
% 2.10/0.63  fof(f70,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(nnf_transformation,[],[f57])).
% 2.10/0.63  fof(f57,plain,(
% 2.10/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(definition_folding,[],[f52,f56])).
% 2.10/0.63  fof(f56,plain,(
% 2.10/0.63    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 2.10/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.10/0.63  fof(f52,plain,(
% 2.10/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(flattening,[],[f51])).
% 2.10/0.63  fof(f51,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(ennf_transformation,[],[f32])).
% 2.10/0.63  fof(f32,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.10/0.63  fof(f107,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 2.10/0.63    inference(cnf_transformation,[],[f69])).
% 2.10/0.63  fof(f69,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 2.10/0.63    inference(rectify,[],[f68])).
% 2.10/0.63  fof(f68,plain,(
% 2.10/0.63    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 2.10/0.63    inference(nnf_transformation,[],[f56])).
% 2.10/0.63  fof(f82,plain,(
% 2.10/0.63    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.10/0.63    inference(cnf_transformation,[],[f16])).
% 2.10/0.63  fof(f16,axiom,(
% 2.10/0.63    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 2.10/0.63  fof(f407,plain,(
% 2.10/0.63    ( ! [X0] : (~r2_hidden(sK1,X0)) )),
% 2.10/0.63    inference(subsumption_resolution,[],[f389,f167])).
% 2.10/0.63  fof(f167,plain,(
% 2.10/0.63    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 2.10/0.63    inference(forward_demodulation,[],[f163,f83])).
% 2.10/0.63  fof(f83,plain,(
% 2.10/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.63    inference(cnf_transformation,[],[f5])).
% 2.10/0.63  fof(f5,axiom,(
% 2.10/0.63    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.10/0.63  fof(f163,plain,(
% 2.10/0.63    ( ! [X6] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X6)) )),
% 2.10/0.63    inference(superposition,[],[f92,f151])).
% 2.10/0.63  fof(f151,plain,(
% 2.10/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.10/0.63    inference(superposition,[],[f149,f81])).
% 2.10/0.63  fof(f81,plain,(
% 2.10/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f4])).
% 2.10/0.63  fof(f4,axiom,(
% 2.10/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.10/0.63  fof(f149,plain,(
% 2.10/0.63    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 2.10/0.63    inference(superposition,[],[f136,f90])).
% 2.10/0.63  fof(f90,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f20])).
% 2.10/0.63  fof(f20,axiom,(
% 2.10/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.10/0.63  fof(f136,plain,(
% 2.10/0.63    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k1_setfam_1(k2_tarski(X2,X1))) )),
% 2.10/0.63    inference(superposition,[],[f90,f89])).
% 2.10/0.63  fof(f89,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f6])).
% 2.10/0.63  fof(f6,axiom,(
% 2.10/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.10/0.63  fof(f92,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f3])).
% 2.10/0.63  fof(f3,axiom,(
% 2.10/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.10/0.63  fof(f389,plain,(
% 2.10/0.63    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) | ~r2_hidden(sK1,X0)) )),
% 2.10/0.63    inference(superposition,[],[f101,f386])).
% 2.10/0.63  fof(f140,plain,(
% 2.10/0.63    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.10/0.63    inference(subsumption_resolution,[],[f138,f79])).
% 2.10/0.63  fof(f79,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f17])).
% 2.10/0.63  fof(f17,axiom,(
% 2.10/0.63    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.10/0.63  fof(f138,plain,(
% 2.10/0.63    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.10/0.63    inference(resolution,[],[f95,f80])).
% 2.10/0.63  fof(f95,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f43])).
% 2.10/0.63  fof(f43,plain,(
% 2.10/0.63    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.10/0.63    inference(flattening,[],[f42])).
% 2.10/0.63  fof(f42,plain,(
% 2.10/0.63    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.10/0.63    inference(ennf_transformation,[],[f21])).
% 2.10/0.63  fof(f21,axiom,(
% 2.10/0.63    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.10/0.63  % SZS output end Proof for theBenchmark
% 2.10/0.63  % (15610)------------------------------
% 2.10/0.63  % (15610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.63  % (15610)Termination reason: Refutation
% 2.10/0.63  
% 2.10/0.63  % (15610)Memory used [KB]: 6524
% 2.10/0.63  % (15610)Time elapsed: 0.231 s
% 2.10/0.63  % (15610)------------------------------
% 2.10/0.63  % (15610)------------------------------
% 2.10/0.63  % (15602)Success in time 0.275 s
%------------------------------------------------------------------------------
