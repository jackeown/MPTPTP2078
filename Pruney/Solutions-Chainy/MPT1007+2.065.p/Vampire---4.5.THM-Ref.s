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
% DateTime   : Thu Dec  3 13:04:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 263 expanded)
%              Number of leaves         :   11 (  64 expanded)
%              Depth                    :   21
%              Number of atoms          :  256 (1213 expanded)
%              Number of equality atoms :   62 ( 276 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(subsumption_resolution,[],[f138,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f44,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f138,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f135,f91])).

fof(f91,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f89,f34])).

fof(f34,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).

fof(f23,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f88,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f87,f31])).

fof(f31,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f86,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f135,plain,
    ( r2_hidden(sK0,k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f41,f118])).

fof(f118,plain,(
    sK0 = sK3(k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f117,f57])).

fof(f117,plain,
    ( sK0 = sK3(k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f102,f41])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | sK0 = X0 ) ),
    inference(resolution,[],[f95,f76])).

fof(f76,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK2))
      | sK0 = X7 ) ),
    inference(subsumption_resolution,[],[f75,f58])).

fof(f58,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f75,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | sK0 = X7 ) ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f70,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | sK0 = X7 ) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK0 = X0 ) ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f94,f58])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f92,f90])).

fof(f90,plain,(
    ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(resolution,[],[f84,f66])).

fof(f66,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f65,f58])).

fof(f65,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f64,f30])).

fof(f64,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f34,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f74,f34])).

fof(f74,plain,(
    ! [X6] :
      ( r2_hidden(k1_funct_1(sK2,X6),sK1)
      | ~ r2_hidden(X6,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f73,f58])).

fof(f73,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X6),sK1) ) ),
    inference(subsumption_resolution,[],[f69,f30])).

fof(f69,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X6),sK1) ) ),
    inference(resolution,[],[f55,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f51,f59])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f89,f53])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (29041)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.50  % (29027)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (29025)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (29043)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (29025)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (29022)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (29033)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f138,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.21/0.51    inference(superposition,[],[f44,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f135,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.21/0.51    inference(resolution,[],[f89,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)) )),
% 0.21/0.51    inference(resolution,[],[f49,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    r2_hidden(sK0,k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.51    inference(superposition,[],[f41,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    sK0 = sK3(k1_tarski(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f57])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    sK0 = sK3(k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.51    inference(resolution,[],[f102,f41])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | sK0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f95,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | sK0 = X7) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f75,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f48,f32])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | sK0 = X7) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f30])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK0 = X7) )),
% 0.21/0.51    inference(resolution,[],[f55,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f50,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.51    inference(resolution,[],[f46,f32])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | X0 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.21/0.51    inference(nnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f94,f58])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f30])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ~r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.51    inference(resolution,[],[f84,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f65,f58])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ~r2_hidden(k1_xboole_0,sK1) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f64,f30])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ~r2_hidden(k1_xboole_0,sK1) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f34,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f74,f34])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X6] : (r2_hidden(k1_funct_1(sK2,X6),sK1) | ~r2_hidden(X6,k1_relat_1(sK2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f73,f58])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X6] : (~r2_hidden(X6,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r2_hidden(k1_funct_1(sK2,X6),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f30])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X6] : (~r2_hidden(X6,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(k1_funct_1(sK2,X6),sK1)) )),
% 0.21/0.51    inference(resolution,[],[f55,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK2) | r2_hidden(X0,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f51,f59])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(k1_xboole_0,sK1) | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(superposition,[],[f89,f53])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (29025)------------------------------
% 0.21/0.51  % (29025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29025)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (29025)Memory used [KB]: 1791
% 0.21/0.51  % (29025)Time elapsed: 0.090 s
% 0.21/0.51  % (29025)------------------------------
% 0.21/0.51  % (29025)------------------------------
% 0.21/0.52  % (29035)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (29015)Success in time 0.149 s
%------------------------------------------------------------------------------
