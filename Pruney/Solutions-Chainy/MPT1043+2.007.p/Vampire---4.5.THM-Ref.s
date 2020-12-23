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
% DateTime   : Thu Dec  3 13:06:58 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  153 (8315 expanded)
%              Number of leaves         :   14 (2000 expanded)
%              Depth                    :   33
%              Number of atoms          :  377 (28560 expanded)
%              Number of equality atoms :   49 (1684 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1788,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1772,f1433])).

fof(f1433,plain,(
    r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1432,f742])).

fof(f742,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f42,f741])).

fof(f741,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f740,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f740,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f739,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f739,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,k1_xboole_0),k1_zfmisc_1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f738,f482])).

fof(f482,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f481,f285])).

fof(f285,plain,(
    v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    inference(resolution,[],[f105,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f43,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

fof(f105,plain,(
    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f44,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f44,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f481,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f480,f294])).

fof(f294,plain,(
    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f293,f42])).

fof(f293,plain,
    ( m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f288,f43])).

fof(f288,plain,
    ( m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f105,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f480,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f479,f106])).

fof(f106,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f44,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f479,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    inference(resolution,[],[f284,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(f284,plain,(
    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1) ),
    inference(resolution,[],[f105,f91])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_2(X1,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f82,plain,(
    ! [X1] :
      ( v1_funct_2(X1,sK0,sK1)
      | ~ r2_hidden(X1,k5_partfun1(sK0,sK1,sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f43,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f738,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(sK2)) ),
    inference(forward_demodulation,[],[f520,f70])).

fof(f520,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(sK2)) ),
    inference(backward_demodulation,[],[f124,f482])).

fof(f124,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(sK2))
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f100,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f100,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f89,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f43,f55])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f1432,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1426,f46])).

fof(f1426,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f1424,f72])).

fof(f72,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1424,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1423,f742])).

fof(f1423,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1413,f46])).

fof(f1413,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f1396,f64])).

fof(f1396,plain,(
    r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f1333,f1386])).

fof(f1386,plain,(
    k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f1382,f1078])).

fof(f1078,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1,k1_xboole_0),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f1033,f53])).

fof(f1033,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f1026,f51])).

fof(f1026,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f768,f53])).

fof(f768,plain,(
    ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f714,f741])).

fof(f714,plain,(
    ! [X3] : ~ r2_hidden(X3,sK2) ),
    inference(subsumption_resolution,[],[f713,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f713,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(forward_demodulation,[],[f486,f70])).

fof(f486,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
      | ~ r2_hidden(X3,sK2) ) ),
    inference(backward_demodulation,[],[f87,f482])).

fof(f87,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f43,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f1382,plain,(
    ! [X8] : ~ r2_hidden(X8,sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1377,f1186])).

fof(f1186,plain,(
    ~ v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f991,f1134])).

fof(f1134,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1127,f1033])).

fof(f1127,plain,(
    ! [X2] : r1_tarski(sK0,X2) ),
    inference(resolution,[],[f1120,f53])).

fof(f1120,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(resolution,[],[f1118,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1118,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,sK0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f1022,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1022,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f994,f67])).

fof(f994,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f593,f45])).

fof(f593,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK0) ),
    inference(backward_demodulation,[],[f312,f482])).

fof(f312,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f307,f94])).

fof(f94,plain,
    ( v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,
    ( v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f43,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

fof(f307,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f303,f69])).

fof(f303,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f290,f56])).

fof(f290,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f105,f67])).

fof(f991,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f590,f741])).

fof(f590,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f307,f482])).

fof(f1377,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0))
      | v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ) ),
    inference(resolution,[],[f1157,f1060])).

fof(f1060,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1,k1_xboole_0),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f1052,f53])).

fof(f1052,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f824,f56])).

fof(f824,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X4) ) ),
    inference(forward_demodulation,[],[f775,f70])).

fof(f775,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,k1_xboole_0)))
      | v1_xboole_0(X4) ) ),
    inference(backward_demodulation,[],[f723,f741])).

fof(f723,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) ) ),
    inference(subsumption_resolution,[],[f496,f45])).

fof(f496,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) ) ),
    inference(backward_demodulation,[],[f97,f482])).

fof(f97,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(sK1)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) ) ),
    inference(resolution,[],[f86,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f86,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f43,f47])).

fof(f1157,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X10,X9) ) ),
    inference(backward_demodulation,[],[f859,f1134])).

fof(f859,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X10,X9) ) ),
    inference(forward_demodulation,[],[f858,f482])).

fof(f858,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k5_partfun1(sK0,sK1,k1_xboole_0))
      | ~ r2_hidden(X10,X9) ) ),
    inference(forward_demodulation,[],[f857,f741])).

fof(f857,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k5_partfun1(sK0,sK1,sK2))
      | ~ r2_hidden(X10,X9) ) ),
    inference(subsumption_resolution,[],[f856,f45])).

fof(f856,plain,(
    ! [X10,X9] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X9,k5_partfun1(sK0,sK1,sK2))
      | ~ r2_hidden(X10,X9) ) ),
    inference(forward_demodulation,[],[f536,f70])).

fof(f536,plain,(
    ! [X10,X9] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
      | ~ r2_hidden(X9,k5_partfun1(sK0,sK1,sK2))
      | ~ r2_hidden(X10,X9) ) ),
    inference(backward_demodulation,[],[f153,f482])).

fof(f153,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k5_partfun1(sK0,sK1,sK2))
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X10,X9) ) ),
    inference(resolution,[],[f92,f67])).

fof(f92,plain,(
    ! [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X2,k5_partfun1(sK0,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f83,plain,(
    ! [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X2,k5_partfun1(sK0,sK1,sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f43,f65])).

fof(f1333,plain,(
    r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0),k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f1282,f1139])).

fof(f1139,plain,(
    ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f760,f1134])).

fof(f760,plain,(
    ~ r1_tarski(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f484,f741])).

fof(f484,plain,(
    ~ r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f44,f482])).

fof(f1282,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK3(X10,k1_xboole_0),X10)
      | r1_tarski(X10,X11) ) ),
    inference(resolution,[],[f1069,f53])).

fof(f1069,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | r2_hidden(sK3(X5,k1_xboole_0),X5) ) ),
    inference(resolution,[],[f1025,f53])).

fof(f1025,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f768,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1772,plain,(
    ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f1142,f1760])).

fof(f1760,plain,(
    k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f1168,f1033])).

fof(f1168,plain,(
    r1_tarski(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f944,f1134])).

fof(f944,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f943,f741])).

fof(f943,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f572,f70])).

fof(f572,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f283,f482])).

fof(f283,plain,(
    r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f105,f155])).

fof(f155,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,k5_partfun1(sK0,sK1,sK2))
      | r1_tarski(X13,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f92,f55])).

fof(f1142,plain,(
    ~ r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f764,f1134])).

fof(f764,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f503,f741])).

fof(f503,plain,(
    ~ r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f106,f482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:21:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (26036)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (26028)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (26017)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (26020)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (26016)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (26025)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (26033)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (26019)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (26018)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (26040)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (26038)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (26013)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.53  % (26023)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.53  % (26041)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.24/0.53  % (26034)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.53  % (26030)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.53  % (26026)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.53  % (26037)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.53  % (26015)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (26015)Refutation not found, incomplete strategy% (26015)------------------------------
% 1.24/0.53  % (26015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (26015)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (26015)Memory used [KB]: 10746
% 1.24/0.53  % (26015)Time elapsed: 0.117 s
% 1.24/0.53  % (26015)------------------------------
% 1.24/0.53  % (26015)------------------------------
% 1.24/0.54  % (26032)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.54  % (26027)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.54  % (26035)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.24/0.54  % (26031)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.54  % (26021)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.54  % (26014)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.54  % (26035)Refutation not found, incomplete strategy% (26035)------------------------------
% 1.24/0.54  % (26035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (26035)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (26035)Memory used [KB]: 10746
% 1.24/0.54  % (26035)Time elapsed: 0.131 s
% 1.24/0.54  % (26035)------------------------------
% 1.24/0.54  % (26035)------------------------------
% 1.24/0.54  % (26022)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.55  % (26039)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.55  % (26042)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.55  % (26024)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.56  % (26029)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.61  % (26039)Refutation not found, incomplete strategy% (26039)------------------------------
% 1.39/0.61  % (26039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.62  % (26036)Refutation found. Thanks to Tanya!
% 1.39/0.62  % SZS status Theorem for theBenchmark
% 1.39/0.62  % SZS output start Proof for theBenchmark
% 1.39/0.62  fof(f1788,plain,(
% 1.39/0.62    $false),
% 1.39/0.62    inference(subsumption_resolution,[],[f1772,f1433])).
% 1.39/0.62  fof(f1433,plain,(
% 1.39/0.62    r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.39/0.62    inference(subsumption_resolution,[],[f1432,f742])).
% 1.39/0.62  fof(f742,plain,(
% 1.39/0.62    v1_funct_1(k1_xboole_0)),
% 1.39/0.62    inference(backward_demodulation,[],[f42,f741])).
% 1.39/0.62  fof(f741,plain,(
% 1.39/0.62    k1_xboole_0 = sK2),
% 1.39/0.62    inference(subsumption_resolution,[],[f740,f46])).
% 1.39/0.62  fof(f46,plain,(
% 1.39/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.39/0.62    inference(cnf_transformation,[],[f5])).
% 1.39/0.62  fof(f5,axiom,(
% 1.39/0.62    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.39/0.62  fof(f740,plain,(
% 1.39/0.62    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) | k1_xboole_0 = sK2),
% 1.39/0.62    inference(forward_demodulation,[],[f739,f70])).
% 1.39/0.62  fof(f70,plain,(
% 1.39/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.62    inference(equality_resolution,[],[f59])).
% 1.39/0.62  fof(f59,plain,(
% 1.39/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.39/0.62    inference(cnf_transformation,[],[f41])).
% 1.39/0.62  fof(f41,plain,(
% 1.39/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.62    inference(flattening,[],[f40])).
% 1.39/0.62  fof(f40,plain,(
% 1.39/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.62    inference(nnf_transformation,[],[f4])).
% 1.39/0.62  fof(f4,axiom,(
% 1.39/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.62  fof(f739,plain,(
% 1.39/0.62    ~m1_subset_1(k2_zfmisc_1(sK0,k1_xboole_0),k1_zfmisc_1(sK2)) | k1_xboole_0 = sK2),
% 1.39/0.62    inference(forward_demodulation,[],[f738,f482])).
% 1.39/0.62  fof(f482,plain,(
% 1.39/0.62    k1_xboole_0 = sK1),
% 1.39/0.62    inference(subsumption_resolution,[],[f481,f285])).
% 1.39/0.62  fof(f285,plain,(
% 1.39/0.62    v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))),
% 1.39/0.62    inference(resolution,[],[f105,f90])).
% 1.39/0.62  fof(f90,plain,(
% 1.39/0.62    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,sK1,sK2)) | v1_funct_1(X0)) )),
% 1.39/0.62    inference(subsumption_resolution,[],[f81,f42])).
% 1.39/0.62  fof(f81,plain,(
% 1.39/0.62    ( ! [X0] : (v1_funct_1(X0) | ~r2_hidden(X0,k5_partfun1(sK0,sK1,sK2)) | ~v1_funct_1(sK2)) )),
% 1.39/0.62    inference(resolution,[],[f43,f63])).
% 1.39/0.62  fof(f63,plain,(
% 1.39/0.62    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f27])).
% 1.39/0.62  fof(f27,plain,(
% 1.39/0.62    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.39/0.62    inference(flattening,[],[f26])).
% 1.39/0.62  fof(f26,plain,(
% 1.39/0.62    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.39/0.62    inference(ennf_transformation,[],[f13])).
% 1.39/0.62  fof(f13,axiom,(
% 1.39/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 1.39/0.62  fof(f43,plain,(
% 1.39/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.62    inference(cnf_transformation,[],[f32])).
% 1.39/0.62  fof(f32,plain,(
% 1.39/0.62    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 1.39/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31])).
% 1.39/0.62  fof(f31,plain,(
% 1.39/0.62    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 1.39/0.62    introduced(choice_axiom,[])).
% 1.39/0.62  fof(f17,plain,(
% 1.39/0.62    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.39/0.62    inference(flattening,[],[f16])).
% 1.39/0.62  fof(f16,plain,(
% 1.39/0.62    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.39/0.62    inference(ennf_transformation,[],[f15])).
% 1.39/0.62  fof(f15,negated_conjecture,(
% 1.39/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.39/0.62    inference(negated_conjecture,[],[f14])).
% 1.39/0.62  fof(f14,conjecture,(
% 1.39/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).
% 1.39/0.62  fof(f105,plain,(
% 1.39/0.62    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))),
% 1.39/0.62    inference(resolution,[],[f44,f53])).
% 1.39/0.62  fof(f53,plain,(
% 1.39/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f38])).
% 1.39/0.62  fof(f38,plain,(
% 1.39/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.39/0.62  fof(f37,plain,(
% 1.39/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.39/0.62    introduced(choice_axiom,[])).
% 1.39/0.62  fof(f36,plain,(
% 1.39/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.62    inference(rectify,[],[f35])).
% 1.39/0.62  fof(f35,plain,(
% 1.39/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.62    inference(nnf_transformation,[],[f21])).
% 1.39/0.62  fof(f21,plain,(
% 1.39/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.62    inference(ennf_transformation,[],[f1])).
% 1.39/0.62  fof(f1,axiom,(
% 1.39/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.62  fof(f44,plain,(
% 1.39/0.62    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 1.39/0.62    inference(cnf_transformation,[],[f32])).
% 1.39/0.62  fof(f481,plain,(
% 1.39/0.62    k1_xboole_0 = sK1 | ~v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))),
% 1.39/0.62    inference(subsumption_resolution,[],[f480,f294])).
% 1.39/0.62  fof(f294,plain,(
% 1.39/0.62    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.62    inference(subsumption_resolution,[],[f293,f42])).
% 1.39/0.62  fof(f293,plain,(
% 1.39/0.62    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.39/0.62    inference(subsumption_resolution,[],[f288,f43])).
% 1.39/0.62  fof(f288,plain,(
% 1.39/0.62    m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.39/0.62    inference(resolution,[],[f105,f65])).
% 1.39/0.62  fof(f65,plain,(
% 1.39/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f27])).
% 1.39/0.62  fof(f480,plain,(
% 1.39/0.62    k1_xboole_0 = sK1 | ~m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))),
% 1.39/0.62    inference(subsumption_resolution,[],[f479,f106])).
% 1.39/0.62  fof(f106,plain,(
% 1.39/0.62    ~r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))),
% 1.39/0.62    inference(resolution,[],[f44,f54])).
% 1.39/0.62  fof(f54,plain,(
% 1.39/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f38])).
% 1.39/0.62  fof(f479,plain,(
% 1.39/0.62    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))),
% 1.39/0.62    inference(resolution,[],[f284,f61])).
% 1.39/0.62  fof(f61,plain,(
% 1.39/0.62    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f25])).
% 1.39/0.62  fof(f25,plain,(
% 1.39/0.62    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.39/0.62    inference(flattening,[],[f24])).
% 1.39/0.62  fof(f24,plain,(
% 1.39/0.62    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.39/0.62    inference(ennf_transformation,[],[f11])).
% 1.39/0.62  fof(f11,axiom,(
% 1.39/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).
% 1.39/0.62  fof(f284,plain,(
% 1.39/0.62    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)),
% 1.39/0.62    inference(resolution,[],[f105,f91])).
% 1.39/0.62  fof(f91,plain,(
% 1.39/0.62    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,sK1,sK2)) | v1_funct_2(X1,sK0,sK1)) )),
% 1.39/0.62    inference(subsumption_resolution,[],[f82,f42])).
% 1.39/0.62  fof(f82,plain,(
% 1.39/0.62    ( ! [X1] : (v1_funct_2(X1,sK0,sK1) | ~r2_hidden(X1,k5_partfun1(sK0,sK1,sK2)) | ~v1_funct_1(sK2)) )),
% 1.39/0.62    inference(resolution,[],[f43,f64])).
% 1.39/0.62  fof(f64,plain,(
% 1.39/0.62    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f27])).
% 1.39/0.62  fof(f738,plain,(
% 1.39/0.62    k1_xboole_0 = sK2 | ~m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(sK2))),
% 1.39/0.62    inference(forward_demodulation,[],[f520,f70])).
% 1.39/0.62  fof(f520,plain,(
% 1.39/0.62    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | ~m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(sK2))),
% 1.39/0.62    inference(backward_demodulation,[],[f124,f482])).
% 1.39/0.62  fof(f124,plain,(
% 1.39/0.62    ~m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(sK2)) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.62    inference(resolution,[],[f100,f55])).
% 1.39/0.62  fof(f55,plain,(
% 1.39/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.39/0.62    inference(cnf_transformation,[],[f39])).
% 1.39/0.62  fof(f39,plain,(
% 1.39/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.39/0.62    inference(nnf_transformation,[],[f6])).
% 1.39/0.62  fof(f6,axiom,(
% 1.39/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.62  fof(f100,plain,(
% 1.39/0.62    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.62    inference(resolution,[],[f89,f51])).
% 1.39/0.62  fof(f51,plain,(
% 1.39/0.62    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f34])).
% 1.39/0.62  fof(f34,plain,(
% 1.39/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.62    inference(flattening,[],[f33])).
% 1.39/0.62  fof(f33,plain,(
% 1.39/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.62    inference(nnf_transformation,[],[f3])).
% 1.39/0.62  fof(f3,axiom,(
% 1.39/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.62  fof(f89,plain,(
% 1.39/0.62    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.39/0.62    inference(resolution,[],[f43,f55])).
% 1.39/0.62  fof(f42,plain,(
% 1.39/0.62    v1_funct_1(sK2)),
% 1.39/0.62    inference(cnf_transformation,[],[f32])).
% 1.39/0.62  fof(f1432,plain,(
% 1.39/0.62    r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~v1_funct_1(k1_xboole_0)),
% 1.39/0.62    inference(subsumption_resolution,[],[f1426,f46])).
% 1.39/0.62  fof(f1426,plain,(
% 1.39/0.62    r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k1_xboole_0)),
% 1.39/0.62    inference(resolution,[],[f1424,f72])).
% 1.39/0.62  fof(f72,plain,(
% 1.39/0.62    ( ! [X2,X1] : (r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 1.39/0.62    inference(equality_resolution,[],[f62])).
% 1.39/0.62  fof(f62,plain,(
% 1.39/0.62    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f25])).
% 1.39/0.62  fof(f1424,plain,(
% 1.39/0.62    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.39/0.62    inference(subsumption_resolution,[],[f1423,f742])).
% 1.39/0.62  fof(f1423,plain,(
% 1.39/0.62    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0)),
% 1.39/0.62    inference(subsumption_resolution,[],[f1413,f46])).
% 1.39/0.62  fof(f1413,plain,(
% 1.39/0.62    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k1_xboole_0)),
% 1.39/0.62    inference(resolution,[],[f1396,f64])).
% 1.39/0.62  fof(f1396,plain,(
% 1.39/0.62    r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f1333,f1386])).
% 1.39/0.62  fof(f1386,plain,(
% 1.39/0.62    k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.39/0.62    inference(resolution,[],[f1382,f1078])).
% 1.39/0.62  fof(f1078,plain,(
% 1.39/0.62    ( ! [X1] : (r2_hidden(sK3(X1,k1_xboole_0),X1) | k1_xboole_0 = X1) )),
% 1.39/0.62    inference(resolution,[],[f1033,f53])).
% 1.39/0.62  fof(f1033,plain,(
% 1.39/0.62    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 1.39/0.62    inference(resolution,[],[f1026,f51])).
% 1.39/0.62  fof(f1026,plain,(
% 1.39/0.62    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.39/0.62    inference(resolution,[],[f768,f53])).
% 1.39/0.62  fof(f768,plain,(
% 1.39/0.62    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) )),
% 1.39/0.62    inference(backward_demodulation,[],[f714,f741])).
% 1.39/0.62  fof(f714,plain,(
% 1.39/0.62    ( ! [X3] : (~r2_hidden(X3,sK2)) )),
% 1.39/0.62    inference(subsumption_resolution,[],[f713,f45])).
% 1.39/0.62  fof(f45,plain,(
% 1.39/0.62    v1_xboole_0(k1_xboole_0)),
% 1.39/0.62    inference(cnf_transformation,[],[f2])).
% 1.39/0.62  fof(f2,axiom,(
% 1.39/0.62    v1_xboole_0(k1_xboole_0)),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.39/0.62  fof(f713,plain,(
% 1.39/0.62    ( ! [X3] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X3,sK2)) )),
% 1.39/0.62    inference(forward_demodulation,[],[f486,f70])).
% 1.39/0.62  fof(f486,plain,(
% 1.39/0.62    ( ! [X3] : (~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | ~r2_hidden(X3,sK2)) )),
% 1.39/0.62    inference(backward_demodulation,[],[f87,f482])).
% 1.39/0.62  fof(f87,plain,(
% 1.39/0.62    ( ! [X3] : (~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X3,sK2)) )),
% 1.39/0.62    inference(resolution,[],[f43,f67])).
% 1.39/0.62  fof(f67,plain,(
% 1.39/0.62    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f30])).
% 1.39/0.62  fof(f30,plain,(
% 1.39/0.62    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.39/0.62    inference(ennf_transformation,[],[f8])).
% 1.39/0.62  fof(f8,axiom,(
% 1.39/0.62    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.39/0.62  fof(f1382,plain,(
% 1.39/0.62    ( ! [X8] : (~r2_hidden(X8,sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0))) )),
% 1.39/0.62    inference(subsumption_resolution,[],[f1377,f1186])).
% 1.39/0.62  fof(f1186,plain,(
% 1.39/0.62    ~v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f991,f1134])).
% 1.39/0.62  fof(f1134,plain,(
% 1.39/0.62    k1_xboole_0 = sK0),
% 1.39/0.62    inference(resolution,[],[f1127,f1033])).
% 1.39/0.62  fof(f1127,plain,(
% 1.39/0.62    ( ! [X2] : (r1_tarski(sK0,X2)) )),
% 1.39/0.62    inference(resolution,[],[f1120,f53])).
% 1.39/0.62  fof(f1120,plain,(
% 1.39/0.62    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.39/0.62    inference(resolution,[],[f1118,f69])).
% 1.39/0.62  fof(f69,plain,(
% 1.39/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.62    inference(equality_resolution,[],[f49])).
% 1.39/0.62  fof(f49,plain,(
% 1.39/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.39/0.62    inference(cnf_transformation,[],[f34])).
% 1.39/0.62  fof(f1118,plain,(
% 1.39/0.62    ( ! [X2,X1] : (~r1_tarski(X2,sK0) | ~r2_hidden(X1,X2)) )),
% 1.39/0.62    inference(resolution,[],[f1022,f56])).
% 1.39/0.62  fof(f56,plain,(
% 1.39/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f39])).
% 1.39/0.62  fof(f1022,plain,(
% 1.39/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X1,X0)) )),
% 1.39/0.62    inference(resolution,[],[f994,f67])).
% 1.39/0.62  fof(f994,plain,(
% 1.39/0.62    v1_xboole_0(sK0)),
% 1.39/0.62    inference(subsumption_resolution,[],[f593,f45])).
% 1.39/0.62  fof(f593,plain,(
% 1.39/0.62    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK0)),
% 1.39/0.62    inference(backward_demodulation,[],[f312,f482])).
% 1.39/0.62  fof(f312,plain,(
% 1.39/0.62    ~v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 1.39/0.62    inference(resolution,[],[f307,f94])).
% 1.39/0.62  fof(f94,plain,(
% 1.39/0.62    v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) | ~v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 1.39/0.62    inference(subsumption_resolution,[],[f85,f42])).
% 1.39/0.62  fof(f85,plain,(
% 1.39/0.62    v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) | ~v1_funct_1(sK2) | ~v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 1.39/0.62    inference(resolution,[],[f43,f60])).
% 1.39/0.62  fof(f60,plain,(
% 1.39/0.62    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f23])).
% 1.39/0.62  fof(f23,plain,(
% 1.39/0.62    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.39/0.62    inference(flattening,[],[f22])).
% 1.39/0.62  fof(f22,plain,(
% 1.39/0.62    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.39/0.62    inference(ennf_transformation,[],[f10])).
% 1.39/0.62  fof(f10,axiom,(
% 1.39/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).
% 1.39/0.62  fof(f307,plain,(
% 1.39/0.62    ~v1_xboole_0(k5_partfun1(sK0,sK1,sK2))),
% 1.39/0.62    inference(resolution,[],[f303,f69])).
% 1.39/0.62  fof(f303,plain,(
% 1.39/0.62    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) | ~v1_xboole_0(X0)) )),
% 1.39/0.62    inference(resolution,[],[f290,f56])).
% 1.39/0.62  fof(f290,plain,(
% 1.39/0.62    ( ! [X0] : (~m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.39/0.62    inference(resolution,[],[f105,f67])).
% 1.39/0.62  fof(f991,plain,(
% 1.39/0.62    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))),
% 1.39/0.62    inference(forward_demodulation,[],[f590,f741])).
% 1.39/0.62  fof(f590,plain,(
% 1.39/0.62    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,sK2))),
% 1.39/0.62    inference(backward_demodulation,[],[f307,f482])).
% 1.39/0.62  fof(f1377,plain,(
% 1.39/0.62    ( ! [X8] : (~r2_hidden(X8,sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)) | v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) )),
% 1.39/0.62    inference(resolution,[],[f1157,f1060])).
% 1.39/0.62  fof(f1060,plain,(
% 1.39/0.62    ( ! [X1] : (r2_hidden(sK3(X1,k1_xboole_0),X1) | v1_xboole_0(X1)) )),
% 1.39/0.62    inference(resolution,[],[f1052,f53])).
% 1.39/0.62  fof(f1052,plain,(
% 1.39/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.39/0.62    inference(resolution,[],[f824,f56])).
% 1.39/0.62  fof(f824,plain,(
% 1.39/0.62    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X4)) )),
% 1.39/0.62    inference(forward_demodulation,[],[f775,f70])).
% 1.39/0.62  fof(f775,plain,(
% 1.39/0.62    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,k1_xboole_0))) | v1_xboole_0(X4)) )),
% 1.39/0.62    inference(backward_demodulation,[],[f723,f741])).
% 1.39/0.62  fof(f723,plain,(
% 1.39/0.62    ( ! [X4,X5] : (v1_xboole_0(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))) )),
% 1.39/0.62    inference(subsumption_resolution,[],[f496,f45])).
% 1.39/0.62  fof(f496,plain,(
% 1.39/0.62    ( ! [X4,X5] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))) )),
% 1.39/0.62    inference(backward_demodulation,[],[f97,f482])).
% 1.39/0.62  fof(f97,plain,(
% 1.39/0.62    ( ! [X4,X5] : (~v1_xboole_0(sK1) | v1_xboole_0(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))) )),
% 1.39/0.62    inference(resolution,[],[f86,f47])).
% 1.39/0.62  fof(f47,plain,(
% 1.39/0.62    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f18])).
% 1.39/0.62  fof(f18,plain,(
% 1.39/0.62    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.39/0.62    inference(ennf_transformation,[],[f9])).
% 1.39/0.62  fof(f9,axiom,(
% 1.39/0.62    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.39/0.62  fof(f86,plain,(
% 1.39/0.62    v1_xboole_0(sK2) | ~v1_xboole_0(sK1)),
% 1.39/0.62    inference(resolution,[],[f43,f47])).
% 1.39/0.62  fof(f1157,plain,(
% 1.39/0.62    ( ! [X10,X9] : (~r2_hidden(X9,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X10,X9)) )),
% 1.39/0.62    inference(backward_demodulation,[],[f859,f1134])).
% 1.39/0.62  fof(f859,plain,(
% 1.39/0.62    ( ! [X10,X9] : (~r2_hidden(X9,k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X10,X9)) )),
% 1.39/0.62    inference(forward_demodulation,[],[f858,f482])).
% 1.39/0.62  fof(f858,plain,(
% 1.39/0.62    ( ! [X10,X9] : (~r2_hidden(X9,k5_partfun1(sK0,sK1,k1_xboole_0)) | ~r2_hidden(X10,X9)) )),
% 1.39/0.62    inference(forward_demodulation,[],[f857,f741])).
% 1.39/0.62  fof(f857,plain,(
% 1.39/0.62    ( ! [X10,X9] : (~r2_hidden(X9,k5_partfun1(sK0,sK1,sK2)) | ~r2_hidden(X10,X9)) )),
% 1.39/0.62    inference(subsumption_resolution,[],[f856,f45])).
% 1.39/0.62  fof(f856,plain,(
% 1.39/0.62    ( ! [X10,X9] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X9,k5_partfun1(sK0,sK1,sK2)) | ~r2_hidden(X10,X9)) )),
% 1.39/0.62    inference(forward_demodulation,[],[f536,f70])).
% 1.39/0.62  fof(f536,plain,(
% 1.39/0.62    ( ! [X10,X9] : (~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | ~r2_hidden(X9,k5_partfun1(sK0,sK1,sK2)) | ~r2_hidden(X10,X9)) )),
% 1.39/0.62    inference(backward_demodulation,[],[f153,f482])).
% 1.39/0.62  fof(f153,plain,(
% 1.39/0.62    ( ! [X10,X9] : (~r2_hidden(X9,k5_partfun1(sK0,sK1,sK2)) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X10,X9)) )),
% 1.39/0.62    inference(resolution,[],[f92,f67])).
% 1.39/0.62  fof(f92,plain,(
% 1.39/0.62    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X2,k5_partfun1(sK0,sK1,sK2))) )),
% 1.39/0.62    inference(subsumption_resolution,[],[f83,f42])).
% 1.39/0.62  fof(f83,plain,(
% 1.39/0.62    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X2,k5_partfun1(sK0,sK1,sK2)) | ~v1_funct_1(sK2)) )),
% 1.39/0.62    inference(resolution,[],[f43,f65])).
% 1.39/0.62  fof(f1333,plain,(
% 1.39/0.62    r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0),k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.39/0.62    inference(resolution,[],[f1282,f1139])).
% 1.39/0.62  fof(f1139,plain,(
% 1.39/0.62    ~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f760,f1134])).
% 1.39/0.62  fof(f760,plain,(
% 1.39/0.62    ~r1_tarski(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f484,f741])).
% 1.39/0.62  fof(f484,plain,(
% 1.39/0.62    ~r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f44,f482])).
% 1.39/0.62  fof(f1282,plain,(
% 1.39/0.62    ( ! [X10,X11] : (r2_hidden(sK3(X10,k1_xboole_0),X10) | r1_tarski(X10,X11)) )),
% 1.39/0.62    inference(resolution,[],[f1069,f53])).
% 1.39/0.62  fof(f1069,plain,(
% 1.39/0.62    ( ! [X4,X5] : (~r2_hidden(X4,X5) | r2_hidden(sK3(X5,k1_xboole_0),X5)) )),
% 1.39/0.62    inference(resolution,[],[f1025,f53])).
% 1.39/0.62  fof(f1025,plain,(
% 1.39/0.62    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.39/0.62    inference(resolution,[],[f768,f52])).
% 1.39/0.62  fof(f52,plain,(
% 1.39/0.62    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.39/0.62    inference(cnf_transformation,[],[f38])).
% 1.39/0.62  fof(f1772,plain,(
% 1.39/0.62    ~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f1142,f1760])).
% 1.39/0.62  fof(f1760,plain,(
% 1.39/0.62    k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.39/0.62    inference(resolution,[],[f1168,f1033])).
% 1.39/0.62  fof(f1168,plain,(
% 1.39/0.62    r1_tarski(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 1.39/0.62    inference(backward_demodulation,[],[f944,f1134])).
% 1.39/0.62  fof(f944,plain,(
% 1.39/0.62    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)),
% 1.39/0.62    inference(forward_demodulation,[],[f943,f741])).
% 1.39/0.62  fof(f943,plain,(
% 1.39/0.62    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_xboole_0)),
% 1.39/0.62    inference(forward_demodulation,[],[f572,f70])).
% 1.39/0.62  fof(f572,plain,(
% 1.39/0.62    r1_tarski(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f283,f482])).
% 1.39/0.62  fof(f283,plain,(
% 1.39/0.62    r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 1.39/0.62    inference(resolution,[],[f105,f155])).
% 1.39/0.62  fof(f155,plain,(
% 1.39/0.62    ( ! [X13] : (~r2_hidden(X13,k5_partfun1(sK0,sK1,sK2)) | r1_tarski(X13,k2_zfmisc_1(sK0,sK1))) )),
% 1.39/0.62    inference(resolution,[],[f92,f55])).
% 1.39/0.62  fof(f1142,plain,(
% 1.39/0.62    ~r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f764,f1134])).
% 1.39/0.62  fof(f764,plain,(
% 1.39/0.62    ~r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f503,f741])).
% 1.39/0.62  fof(f503,plain,(
% 1.39/0.62    ~r2_hidden(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)),k1_funct_2(sK0,k1_xboole_0))),
% 1.39/0.62    inference(backward_demodulation,[],[f106,f482])).
% 1.39/0.62  % SZS output end Proof for theBenchmark
% 1.39/0.62  % (26036)------------------------------
% 1.39/0.62  % (26036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.62  % (26036)Termination reason: Refutation
% 1.39/0.62  
% 1.39/0.62  % (26036)Memory used [KB]: 2430
% 1.39/0.62  % (26036)Time elapsed: 0.152 s
% 1.39/0.62  % (26036)------------------------------
% 1.39/0.62  % (26036)------------------------------
% 1.39/0.62  % (26012)Success in time 0.259 s
%------------------------------------------------------------------------------
