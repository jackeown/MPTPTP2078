%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:07 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 596 expanded)
%              Number of leaves         :   19 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          :  245 (2324 expanded)
%              Number of equality atoms :   60 ( 518 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(resolution,[],[f368,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f6,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f368,plain,(
    ! [X1] : ~ m1_subset_1(X1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f361,f357])).

fof(f357,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f348,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
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

fof(f348,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f347,f326])).

fof(f326,plain,(
    ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f285,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f111,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f110,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f110,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | k1_xboole_0 = k1_funct_1(k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f109,f47])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f109,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_relat_1(k1_xboole_0))
      | k1_xboole_0 = k1_funct_1(k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f107,f73])).

fof(f73,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f52,f46])).

fof(f46,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f52,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f107,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | k1_xboole_0 = k1_funct_1(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f70,f74])).

fof(f74,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f51,f46])).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = k1_funct_1(X0,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f285,plain,(
    ~ r2_hidden(k1_funct_1(k1_xboole_0,sK0),sK1) ),
    inference(backward_demodulation,[],[f45,f281])).

fof(f281,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f101,f278])).

fof(f278,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f277,f45])).

fof(f277,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f276,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f34])).

fof(f34,plain,
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

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f276,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f275,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f275,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f274,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f274,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f101,plain,
    ( r2_hidden(sK0,k1_tarski(sK0))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( r2_hidden(sK0,k1_tarski(sK0))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f96,f94])).

fof(f94,plain,
    ( sK0 = k1_mcart_1(sK3(sK2))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f90,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f90,plain,
    ( r2_hidden(sK3(sK2),k2_zfmisc_1(k1_tarski(sK0),sK1))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f87,f57])).

fof(f87,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK2)
      | r2_hidden(X2,k2_zfmisc_1(k1_tarski(sK0),sK1)) ) ),
    inference(resolution,[],[f62,f43])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f96,plain,
    ( r2_hidden(k1_mcart_1(sK3(sK2)),k1_tarski(sK0))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f90,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f45,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f347,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(forward_demodulation,[],[f325,f112])).

fof(f325,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(backward_demodulation,[],[f277,f281])).

fof(f361,plain,(
    ! [X1] : ~ m1_subset_1(X1,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f352,f75])).

fof(f75,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(superposition,[],[f59,f50])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f352,plain,(
    ! [X1] :
      ( v1_xboole_0(k1_tarski(sK0))
      | ~ m1_subset_1(X1,k1_tarski(sK0)) ) ),
    inference(resolution,[],[f348,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:12:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.54  % (30037)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.55  % (30046)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.55  % (30057)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.55  % (30055)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.55  % (30054)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.56  % (30047)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.56  % (30031)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.56  % (30038)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.56  % (30033)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.46/0.56  % (30037)Refutation found. Thanks to Tanya!
% 1.46/0.56  % SZS status Theorem for theBenchmark
% 1.46/0.57  % (30038)Refutation not found, incomplete strategy% (30038)------------------------------
% 1.46/0.57  % (30038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (30038)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (30038)Memory used [KB]: 10746
% 1.46/0.57  % (30038)Time elapsed: 0.130 s
% 1.46/0.57  % (30038)------------------------------
% 1.46/0.57  % (30038)------------------------------
% 1.46/0.57  % (30032)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.57  % (30036)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.46/0.57  % (30049)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.57  % (30041)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.57  % SZS output start Proof for theBenchmark
% 1.46/0.57  fof(f372,plain,(
% 1.46/0.57    $false),
% 1.46/0.57    inference(resolution,[],[f368,f58])).
% 1.46/0.57  fof(f58,plain,(
% 1.46/0.57    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f40])).
% 1.46/0.57  fof(f40,plain,(
% 1.46/0.57    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f6,f39])).
% 1.46/0.57  fof(f39,plain,(
% 1.46/0.57    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f6,axiom,(
% 1.46/0.57    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.46/0.57  fof(f368,plain,(
% 1.46/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_xboole_0)) )),
% 1.46/0.57    inference(backward_demodulation,[],[f361,f357])).
% 1.46/0.57  fof(f357,plain,(
% 1.46/0.57    k1_xboole_0 = k1_tarski(sK0)),
% 1.46/0.57    inference(resolution,[],[f348,f57])).
% 1.46/0.57  fof(f57,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.46/0.57    inference(cnf_transformation,[],[f38])).
% 1.46/0.57  fof(f38,plain,(
% 1.46/0.57    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f37])).
% 1.46/0.57  fof(f37,plain,(
% 1.46/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f25,plain,(
% 1.46/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.46/0.57    inference(ennf_transformation,[],[f20])).
% 1.46/0.57  fof(f20,plain,(
% 1.46/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.46/0.57    inference(pure_predicate_removal,[],[f16])).
% 1.46/0.57  fof(f16,axiom,(
% 1.46/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 1.46/0.57  fof(f348,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f347,f326])).
% 1.46/0.57  fof(f326,plain,(
% 1.46/0.57    ~r2_hidden(k1_xboole_0,sK1)),
% 1.46/0.57    inference(forward_demodulation,[],[f285,f112])).
% 1.46/0.57  fof(f112,plain,(
% 1.46/0.57    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f111,f49])).
% 1.46/0.57  fof(f49,plain,(
% 1.46/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f1])).
% 1.46/0.57  fof(f1,axiom,(
% 1.46/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.46/0.57  fof(f111,plain,(
% 1.46/0.57    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.46/0.57    inference(resolution,[],[f110,f63])).
% 1.46/0.57  fof(f63,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f29])).
% 1.46/0.57  fof(f29,plain,(
% 1.46/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f13])).
% 1.46/0.57  fof(f13,axiom,(
% 1.46/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.46/0.57  fof(f110,plain,(
% 1.46/0.57    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | k1_xboole_0 = k1_funct_1(k1_xboole_0,X2)) )),
% 1.46/0.57    inference(forward_demodulation,[],[f109,f47])).
% 1.46/0.57  fof(f47,plain,(
% 1.46/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.57    inference(cnf_transformation,[],[f9])).
% 1.46/0.57  fof(f9,axiom,(
% 1.46/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.46/0.57  fof(f109,plain,(
% 1.46/0.57    ( ! [X2] : (r2_hidden(X2,k1_relat_1(k1_xboole_0)) | k1_xboole_0 = k1_funct_1(k1_xboole_0,X2)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f107,f73])).
% 1.46/0.57  fof(f73,plain,(
% 1.46/0.57    v1_funct_1(k1_xboole_0)),
% 1.46/0.57    inference(superposition,[],[f52,f46])).
% 1.46/0.57  fof(f46,plain,(
% 1.46/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.46/0.57    inference(cnf_transformation,[],[f10])).
% 1.46/0.57  fof(f10,axiom,(
% 1.46/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.46/0.57  fof(f52,plain,(
% 1.46/0.57    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f12])).
% 1.46/0.57  fof(f12,axiom,(
% 1.46/0.57    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.46/0.57  fof(f107,plain,(
% 1.46/0.57    ( ! [X2] : (r2_hidden(X2,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | k1_xboole_0 = k1_funct_1(k1_xboole_0,X2)) )),
% 1.46/0.57    inference(resolution,[],[f70,f74])).
% 1.46/0.57  fof(f74,plain,(
% 1.46/0.57    v1_relat_1(k1_xboole_0)),
% 1.46/0.57    inference(superposition,[],[f51,f46])).
% 1.46/0.57  fof(f51,plain,(
% 1.46/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f12])).
% 1.46/0.57  fof(f70,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | k1_xboole_0 = k1_funct_1(X0,X1)) )),
% 1.46/0.57    inference(equality_resolution,[],[f56])).
% 1.46/0.57  fof(f56,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f36])).
% 1.46/0.57  fof(f36,plain,(
% 1.46/0.57    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.57    inference(nnf_transformation,[],[f24])).
% 1.46/0.57  fof(f24,plain,(
% 1.46/0.57    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.57    inference(flattening,[],[f23])).
% 1.46/0.57  fof(f23,plain,(
% 1.46/0.57    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f11])).
% 1.46/0.57  fof(f11,axiom,(
% 1.46/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 1.46/0.57  fof(f285,plain,(
% 1.46/0.57    ~r2_hidden(k1_funct_1(k1_xboole_0,sK0),sK1)),
% 1.46/0.57    inference(backward_demodulation,[],[f45,f281])).
% 1.46/0.57  fof(f281,plain,(
% 1.46/0.57    k1_xboole_0 = sK2),
% 1.46/0.57    inference(subsumption_resolution,[],[f101,f278])).
% 1.46/0.57  fof(f278,plain,(
% 1.46/0.57    ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.46/0.57    inference(resolution,[],[f277,f45])).
% 1.46/0.57  fof(f277,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f276,f41])).
% 1.46/0.57  fof(f41,plain,(
% 1.46/0.57    v1_funct_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f35])).
% 1.46/0.57  fof(f35,plain,(
% 1.46/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f34])).
% 1.46/0.57  fof(f34,plain,(
% 1.46/0.57    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f22,plain,(
% 1.46/0.57    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.46/0.57    inference(flattening,[],[f21])).
% 1.46/0.57  fof(f21,plain,(
% 1.46/0.57    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.46/0.57    inference(ennf_transformation,[],[f19])).
% 1.46/0.57  fof(f19,negated_conjecture,(
% 1.46/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.46/0.57    inference(negated_conjecture,[],[f18])).
% 1.46/0.57  fof(f18,conjecture,(
% 1.46/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 1.46/0.57  fof(f276,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f275,f43])).
% 1.46/0.57  fof(f43,plain,(
% 1.46/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.46/0.57    inference(cnf_transformation,[],[f35])).
% 1.46/0.57  fof(f275,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f274,f44])).
% 1.46/0.57  fof(f44,plain,(
% 1.46/0.57    k1_xboole_0 != sK1),
% 1.46/0.57    inference(cnf_transformation,[],[f35])).
% 1.46/0.57  fof(f274,plain,(
% 1.46/0.57    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2)) )),
% 1.46/0.57    inference(resolution,[],[f69,f42])).
% 1.46/0.57  fof(f42,plain,(
% 1.46/0.57    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f35])).
% 1.46/0.57  fof(f69,plain,(
% 1.46/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_1(X3)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f33])).
% 1.46/0.57  fof(f33,plain,(
% 1.46/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.46/0.57    inference(flattening,[],[f32])).
% 1.46/0.57  fof(f32,plain,(
% 1.46/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.46/0.57    inference(ennf_transformation,[],[f17])).
% 1.46/0.57  fof(f17,axiom,(
% 1.46/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.46/0.57  fof(f101,plain,(
% 1.46/0.57    r2_hidden(sK0,k1_tarski(sK0)) | k1_xboole_0 = sK2),
% 1.46/0.57    inference(duplicate_literal_removal,[],[f100])).
% 1.46/0.57  fof(f100,plain,(
% 1.46/0.57    r2_hidden(sK0,k1_tarski(sK0)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.46/0.57    inference(superposition,[],[f96,f94])).
% 1.46/0.57  fof(f94,plain,(
% 1.46/0.57    sK0 = k1_mcart_1(sK3(sK2)) | k1_xboole_0 = sK2),
% 1.46/0.57    inference(resolution,[],[f90,f67])).
% 1.46/0.57  fof(f67,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.46/0.57    inference(cnf_transformation,[],[f31])).
% 1.46/0.57  fof(f31,plain,(
% 1.46/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.46/0.57    inference(ennf_transformation,[],[f15])).
% 1.46/0.57  fof(f15,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.46/0.57  fof(f90,plain,(
% 1.46/0.57    r2_hidden(sK3(sK2),k2_zfmisc_1(k1_tarski(sK0),sK1)) | k1_xboole_0 = sK2),
% 1.46/0.57    inference(resolution,[],[f87,f57])).
% 1.46/0.57  fof(f87,plain,(
% 1.46/0.57    ( ! [X2] : (~r2_hidden(X2,sK2) | r2_hidden(X2,k2_zfmisc_1(k1_tarski(sK0),sK1))) )),
% 1.46/0.57    inference(resolution,[],[f62,f43])).
% 1.46/0.57  fof(f62,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f28])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f7])).
% 1.46/0.57  fof(f7,axiom,(
% 1.46/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.46/0.57  fof(f96,plain,(
% 1.46/0.57    r2_hidden(k1_mcart_1(sK3(sK2)),k1_tarski(sK0)) | k1_xboole_0 = sK2),
% 1.46/0.57    inference(resolution,[],[f90,f65])).
% 1.46/0.57  fof(f65,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f30])).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.46/0.57    inference(ennf_transformation,[],[f14])).
% 1.46/0.57  fof(f14,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.46/0.57  fof(f45,plain,(
% 1.46/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f35])).
% 1.46/0.57  fof(f347,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(k1_xboole_0,sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 1.46/0.57    inference(forward_demodulation,[],[f325,f112])).
% 1.46/0.57  fof(f325,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 1.46/0.57    inference(backward_demodulation,[],[f277,f281])).
% 1.46/0.57  fof(f361,plain,(
% 1.46/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_tarski(sK0))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f352,f75])).
% 1.46/0.57  fof(f75,plain,(
% 1.46/0.57    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.46/0.57    inference(superposition,[],[f59,f50])).
% 1.46/0.57  fof(f50,plain,(
% 1.46/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f2])).
% 1.46/0.57  fof(f2,axiom,(
% 1.46/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.46/0.57  fof(f59,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f5])).
% 1.46/0.57  fof(f5,axiom,(
% 1.46/0.57    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).
% 1.46/0.57  fof(f352,plain,(
% 1.46/0.57    ( ! [X1] : (v1_xboole_0(k1_tarski(sK0)) | ~m1_subset_1(X1,k1_tarski(sK0))) )),
% 1.46/0.57    inference(resolution,[],[f348,f61])).
% 1.46/0.57  fof(f61,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f27])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.46/0.57    inference(flattening,[],[f26])).
% 1.46/0.57  fof(f26,plain,(
% 1.46/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f8])).
% 1.46/0.57  fof(f8,axiom,(
% 1.46/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (30037)------------------------------
% 1.46/0.57  % (30037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (30037)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (30037)Memory used [KB]: 6524
% 1.46/0.57  % (30037)Time elapsed: 0.119 s
% 1.46/0.57  % (30037)------------------------------
% 1.46/0.57  % (30037)------------------------------
% 1.46/0.57  % (30029)Success in time 0.201 s
%------------------------------------------------------------------------------
