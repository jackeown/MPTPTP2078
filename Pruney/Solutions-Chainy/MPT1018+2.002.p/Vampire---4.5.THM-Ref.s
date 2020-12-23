%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 850 expanded)
%              Number of leaves         :   10 ( 264 expanded)
%              Depth                    :   23
%              Number of atoms          :  260 (5789 expanded)
%              Number of equality atoms :   76 (1637 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(subsumption_resolution,[],[f277,f213])).

fof(f213,plain,(
    r2_hidden(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f201,f33])).

fof(f33,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f201,plain,
    ( sK2 = sK3
    | r2_hidden(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f101,f188])).

fof(f188,plain,(
    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f187,f111])).

fof(f111,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(superposition,[],[f31,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f97,f32])).

fof(f32,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) ),
    inference(resolution,[],[f66,f31])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f64,f27])).

fof(f27,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f29,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f28,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f187,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(superposition,[],[f86,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f115,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f115,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK1))
    | k1_xboole_0 = k1_relat_1(sK1)
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(superposition,[],[f78,f98])).

fof(f78,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | sK0 = k1_relat_1(sK1) ),
    inference(resolution,[],[f76,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f76,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f75,f63])).

fof(f63,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f75,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f62,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f62,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f86,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK1))
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f85,f63])).

fof(f85,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f84,f26])).

fof(f84,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f81,f29])).

fof(f81,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f37,f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f101,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(superposition,[],[f30,f96])).

fof(f96,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(resolution,[],[f66,f30])).

fof(f30,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f277,plain,(
    ~ r2_hidden(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f224,f252])).

fof(f252,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f247,f34])).

fof(f247,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f216,f41])).

fof(f216,plain,(
    r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f204,f33])).

fof(f204,plain,
    ( sK2 = sK3
    | r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f105,f188])).

fof(f105,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(superposition,[],[f76,f96])).

fof(f224,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f223,f63])).

fof(f223,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f222,f26])).

fof(f222,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f221,f29])).

fof(f221,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f207,f33])).

fof(f207,plain,
    ( sK2 = sK3
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f188,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:38:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (29000)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.44  % (29000)Refutation not found, incomplete strategy% (29000)------------------------------
% 0.22/0.44  % (29000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (29000)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.44  
% 0.22/0.44  % (29000)Memory used [KB]: 10618
% 0.22/0.44  % (29000)Time elapsed: 0.047 s
% 0.22/0.44  % (29000)------------------------------
% 0.22/0.44  % (29000)------------------------------
% 0.22/0.48  % (29008)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.49  % (29018)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.49  % (29001)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.49  % (29008)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f277,f213])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    r2_hidden(sK2,k1_xboole_0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f201,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    sK2 != sK3),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f21,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    sK2 = sK3 | r2_hidden(sK2,k1_xboole_0)),
% 0.22/0.49    inference(backward_demodulation,[],[f101,f188])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f187,f111])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    r2_hidden(sK3,k1_xboole_0) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(superposition,[],[f31,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(forward_demodulation,[],[f97,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))),
% 0.22/0.49    inference(resolution,[],[f66,f31])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f65,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v1_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v1_funct_1(sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f64,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f61,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v2_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.22/0.49    inference(resolution,[],[f28,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    r2_hidden(sK3,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    ~r2_hidden(sK3,k1_xboole_0) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f177])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    ~r2_hidden(sK3,k1_xboole_0) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(superposition,[],[f86,f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(sK1) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f115,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,k1_relat_1(sK1)) | k1_xboole_0 = k1_relat_1(sK1) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(superposition,[],[f78,f98])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ~r1_tarski(sK0,k1_relat_1(sK1)) | sK0 = k1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f76,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f75,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f28,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f62,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    v4_relat_1(sK1,sK0)),
% 0.22/0.49    inference(resolution,[],[f28,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ~r2_hidden(sK3,k1_relat_1(sK1)) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f85,f63])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f84,f26])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f81,f29])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(superposition,[],[f37,f32])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    r2_hidden(sK2,k1_xboole_0) | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(superposition,[],[f30,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(resolution,[],[f66,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    r2_hidden(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    ~r2_hidden(sK2,k1_xboole_0)),
% 0.22/0.49    inference(forward_demodulation,[],[f224,f252])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f247,f34])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(sK1) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f216,f41])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f204,f33])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    sK2 = sK3 | r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 0.22/0.49    inference(backward_demodulation,[],[f105,f188])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(sK1),k1_xboole_0) | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    inference(superposition,[],[f76,f96])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    ~r2_hidden(sK2,k1_relat_1(sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f223,f63])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f222,f26])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f221,f29])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f207,f33])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    sK2 = sK3 | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(superposition,[],[f188,f37])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (29008)------------------------------
% 0.22/0.49  % (29008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (29008)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (29008)Memory used [KB]: 1663
% 0.22/0.49  % (29008)Time elapsed: 0.090 s
% 0.22/0.49  % (29008)------------------------------
% 0.22/0.49  % (29008)------------------------------
% 0.22/0.49  % (29013)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (29025)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (28998)Success in time 0.133 s
%------------------------------------------------------------------------------
