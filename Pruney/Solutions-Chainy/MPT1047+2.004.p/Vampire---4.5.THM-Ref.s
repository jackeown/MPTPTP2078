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
% DateTime   : Thu Dec  3 13:07:01 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  134 (3069 expanded)
%              Number of leaves         :   16 ( 926 expanded)
%              Depth                    :   37
%              Number of atoms          :  521 (17042 expanded)
%              Number of equality atoms :  194 (3903 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2288,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2206,f2141])).

fof(f2141,plain,(
    ! [X0] : k1_xboole_0 = X0 ),
    inference(subsumption_resolution,[],[f2139,f81])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2139,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f55,f685])).

fof(f685,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f681,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f681,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(duplicate_literal_removal,[],[f663])).

fof(f663,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f332,f606])).

fof(f606,plain,
    ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f605,f50])).

fof(f50,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f36,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
          & v1_funct_2(X3,sK0,k1_tarski(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        & v1_funct_2(X3,sK0,k1_tarski(sK1))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f605,plain,
    ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(equality_resolution,[],[f537])).

fof(f537,plain,(
    ! [X93] :
      ( sK3 != X93
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X93)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(duplicate_literal_removal,[],[f534])).

fof(f534,plain,(
    ! [X93] :
      ( sK3 != X93
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X93)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X93)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(superposition,[],[f67,f486])).

% (11375)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f486,plain,(
    ! [X0] :
      ( sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(subsumption_resolution,[],[f485,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f485,plain,(
    ! [X0] :
      ( sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(duplicate_literal_removal,[],[f483])).

fof(f483,plain,(
    ! [X0] :
      ( sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f442,f160])).

fof(f160,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f130,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sK4(X0,X1) != X1
        & r2_hidden(sK4(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK4(X0,X1) != X1
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ) ),
    inference(resolution,[],[f113,f46])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK2))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f442,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(subsumption_resolution,[],[f441,f110])).

fof(f110,plain,
    ( v1_partfun1(sK3,sK0)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f108,f49])).

fof(f108,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f84,f48])).

fof(f48,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f441,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)
      | ~ v1_partfun1(sK3,sK0)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(duplicate_literal_removal,[],[f440])).

fof(f440,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)
      | ~ v1_partfun1(sK3,sK0)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f291,f209])).

fof(f209,plain,(
    ! [X0] :
      ( v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f208,f160])).

fof(f208,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1)
      | ~ m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f207,f123])).

fof(f123,plain,(
    ! [X0] :
      ( v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f117,f66])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | v1_funct_1(X0) ) ),
    inference(resolution,[],[f104,f46])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK2))
      | v1_funct_1(X0) ) ),
    inference(resolution,[],[f71,f45])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f207,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1)
      | ~ m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0)
      | ~ v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) ) ),
    inference(resolution,[],[f158,f84])).

fof(f158,plain,(
    ! [X0] :
      ( v1_funct_2(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f124,f66])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | v1_funct_2(X0,sK0,k1_tarski(sK1)) ) ),
    inference(resolution,[],[f106,f46])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK2))
      | v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f72,f45])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f291,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),X4)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3)
      | ~ v1_partfun1(sK3,X4)
      | k1_tarski(X3) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f290,f123])).

fof(f290,plain,(
    ! [X4,X5,X3] :
      ( k1_tarski(X3) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3)
      | ~ v1_partfun1(sK3,X4)
      | ~ v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),X4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3)) ) ),
    inference(subsumption_resolution,[],[f286,f47])).

fof(f286,plain,(
    ! [X4,X5,X3] :
      ( k1_tarski(X3) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3)
      | ~ v1_partfun1(sK3,X4)
      | ~ v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),X4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3)) ) ),
    inference(resolution,[],[f253,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f253,plain,(
    ! [X0] :
      ( r1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK3)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f252,f49])).

fof(f252,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | r1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK3)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ) ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | r1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK3)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f195,f160])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | r1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK3)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) ) ),
    inference(resolution,[],[f123,f116])).

fof(f116,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(X5)
      | r1_partfun1(X5,sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,k1_tarski(X4))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,k1_tarski(X4)))) ) ),
    inference(resolution,[],[f77,f47])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f332,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,k1_tarski(sK1),sK2),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f330,f50])).

fof(f330,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | ~ r1_tarski(k5_partfun1(sK0,k1_tarski(sK1),sK2),k1_tarski(sK3)) ),
    inference(resolution,[],[f329,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f329,plain,
    ( r1_tarski(k1_tarski(sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(resolution,[],[f249,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f249,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(k5_partfun1(sK0,k1_tarski(sK1),sK2)))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(resolution,[],[f221,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f221,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f220,f46])).

fof(f220,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(subsumption_resolution,[],[f219,f49])).

fof(f219,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(resolution,[],[f192,f48])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK3,X1,X0)
      | r2_hidden(sK3,k5_partfun1(X1,X0,sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f191,f45])).

fof(f191,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3,k5_partfun1(X1,X0,sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK3,X1,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f188,f47])).

fof(f188,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3,k5_partfun1(X1,X0,sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK3,X1,X0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f175,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

fof(f175,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f173,f46])).

fof(f173,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f139,f49])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(sK2,sK3) ) ),
    inference(resolution,[],[f116,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f2206,plain,(
    k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f924,f2141])).

fof(f924,plain,(
    k5_partfun1(sK0,k1_xboole_0,k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(backward_demodulation,[],[f850,f903])).

fof(f903,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f902,f51])).

fof(f902,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f901,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f901,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f900,f685])).

fof(f900,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3) ),
    inference(forward_demodulation,[],[f693,f80])).

fof(f693,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3) ),
    inference(backward_demodulation,[],[f111,f685])).

fof(f111,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3)
    | k2_zfmisc_1(sK0,k1_tarski(sK1)) = sK3 ),
    inference(resolution,[],[f92,f60])).

fof(f92,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_tarski(sK1))) ),
    inference(resolution,[],[f61,f49])).

fof(f850,plain,(
    k1_tarski(sK3) != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f689,f825])).

fof(f825,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f824,f51])).

fof(f824,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f823,f80])).

fof(f823,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f822,f685])).

fof(f822,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2) ),
    inference(forward_demodulation,[],[f692,f80])).

fof(f692,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2) ),
    inference(backward_demodulation,[],[f99,f685])).

fof(f99,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)
    | sK2 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f91,f60])).

fof(f91,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_tarski(sK1))) ),
    inference(resolution,[],[f61,f46])).

fof(f689,plain,(
    k1_tarski(sK3) != k5_partfun1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f50,f685])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (11307)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (11327)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (11317)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (11309)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (11316)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (11306)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (11325)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (11308)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (11311)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (11328)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (11302)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (11305)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (11333)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (11332)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (11330)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (11332)Refutation not found, incomplete strategy% (11332)------------------------------
% 0.21/0.55  % (11332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11332)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11332)Memory used [KB]: 6268
% 0.21/0.55  % (11332)Time elapsed: 0.138 s
% 0.21/0.55  % (11332)------------------------------
% 0.21/0.55  % (11332)------------------------------
% 0.21/0.55  % (11303)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (11304)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (11326)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (11324)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (11319)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (11321)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (11331)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (11334)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (11334)Refutation not found, incomplete strategy% (11334)------------------------------
% 0.21/0.56  % (11334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11334)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11334)Memory used [KB]: 1663
% 0.21/0.56  % (11334)Time elapsed: 0.149 s
% 0.21/0.56  % (11334)------------------------------
% 0.21/0.56  % (11334)------------------------------
% 0.21/0.56  % (11306)Refutation not found, incomplete strategy% (11306)------------------------------
% 0.21/0.56  % (11306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11306)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11306)Memory used [KB]: 1791
% 0.21/0.56  % (11306)Time elapsed: 0.129 s
% 0.21/0.56  % (11306)------------------------------
% 0.21/0.56  % (11306)------------------------------
% 0.21/0.56  % (11314)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (11322)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (11315)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (11312)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (11323)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (11320)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (11329)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.57  % (11329)Refutation not found, incomplete strategy% (11329)------------------------------
% 0.21/0.57  % (11329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (11329)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (11329)Memory used [KB]: 10746
% 0.21/0.57  % (11329)Time elapsed: 0.155 s
% 0.21/0.57  % (11329)------------------------------
% 0.21/0.57  % (11329)------------------------------
% 0.21/0.58  % (11321)Refutation not found, incomplete strategy% (11321)------------------------------
% 0.21/0.58  % (11321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (11321)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (11321)Memory used [KB]: 10746
% 0.21/0.58  % (11321)Time elapsed: 0.148 s
% 0.21/0.58  % (11321)------------------------------
% 0.21/0.58  % (11321)------------------------------
% 2.08/0.67  % (11309)Refutation found. Thanks to Tanya!
% 2.08/0.67  % SZS status Theorem for theBenchmark
% 2.08/0.67  % SZS output start Proof for theBenchmark
% 2.08/0.67  fof(f2288,plain,(
% 2.08/0.67    $false),
% 2.08/0.67    inference(subsumption_resolution,[],[f2206,f2141])).
% 2.08/0.67  fof(f2141,plain,(
% 2.08/0.67    ( ! [X0] : (k1_xboole_0 = X0) )),
% 2.08/0.67    inference(subsumption_resolution,[],[f2139,f81])).
% 2.08/0.67  fof(f81,plain,(
% 2.08/0.67    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.08/0.67    inference(equality_resolution,[],[f64])).
% 2.08/0.67  fof(f64,plain,(
% 2.08/0.67    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.08/0.67    inference(cnf_transformation,[],[f42])).
% 2.08/0.67  fof(f42,plain,(
% 2.08/0.67    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.08/0.67    inference(flattening,[],[f41])).
% 2.08/0.68  fof(f41,plain,(
% 2.08/0.68    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.08/0.68    inference(nnf_transformation,[],[f8])).
% 2.08/0.68  fof(f8,axiom,(
% 2.08/0.68    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.08/0.68  fof(f2139,plain,(
% 2.08/0.68    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 2.08/0.68    inference(superposition,[],[f55,f685])).
% 2.08/0.68  fof(f685,plain,(
% 2.08/0.68    k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(subsumption_resolution,[],[f681,f51])).
% 2.08/0.68  fof(f51,plain,(
% 2.08/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f2])).
% 2.08/0.68  fof(f2,axiom,(
% 2.08/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.08/0.68  fof(f681,plain,(
% 2.08/0.68    ~r1_tarski(k1_xboole_0,k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(duplicate_literal_removal,[],[f663])).
% 2.08/0.68  fof(f663,plain,(
% 2.08/0.68    ~r1_tarski(k1_xboole_0,k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(superposition,[],[f332,f606])).
% 2.08/0.68  fof(f606,plain,(
% 2.08/0.68    k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(subsumption_resolution,[],[f605,f50])).
% 2.08/0.68  fof(f50,plain,(
% 2.08/0.68    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)),
% 2.08/0.68    inference(cnf_transformation,[],[f37])).
% 2.08/0.68  fof(f37,plain,(
% 2.08/0.68    (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2)),
% 2.08/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f36,f35])).
% 2.08/0.68  fof(f35,plain,(
% 2.08/0.68    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2))),
% 2.08/0.68    introduced(choice_axiom,[])).
% 2.08/0.68  fof(f36,plain,(
% 2.08/0.68    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) => (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 2.08/0.68    introduced(choice_axiom,[])).
% 2.08/0.68  fof(f20,plain,(
% 2.08/0.68    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 2.08/0.68    inference(flattening,[],[f19])).
% 2.08/0.68  fof(f19,plain,(
% 2.08/0.68    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 2.08/0.68    inference(ennf_transformation,[],[f18])).
% 2.08/0.68  fof(f18,negated_conjecture,(
% 2.08/0.68    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 2.08/0.68    inference(negated_conjecture,[],[f17])).
% 2.08/0.68  fof(f17,conjecture,(
% 2.08/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).
% 2.08/0.68  fof(f605,plain,(
% 2.08/0.68    k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(equality_resolution,[],[f537])).
% 2.08/0.68  fof(f537,plain,(
% 2.08/0.68    ( ! [X93] : (sK3 != X93 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X93) | k1_xboole_0 = k1_tarski(sK1)) )),
% 2.08/0.68    inference(duplicate_literal_removal,[],[f534])).
% 2.08/0.68  fof(f534,plain,(
% 2.08/0.68    ( ! [X93] : (sK3 != X93 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X93) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X93) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1)) )),
% 2.08/0.68    inference(superposition,[],[f67,f486])).
% 2.08/0.68  % (11375)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.08/0.68  fof(f486,plain,(
% 2.08/0.68    ( ! [X0] : (sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1)) )),
% 2.08/0.68    inference(subsumption_resolution,[],[f485,f49])).
% 2.08/0.68  fof(f49,plain,(
% 2.08/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.08/0.68    inference(cnf_transformation,[],[f37])).
% 2.08/0.68  fof(f485,plain,(
% 2.08/0.68    ( ! [X0] : (sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1)) )),
% 2.08/0.68    inference(duplicate_literal_removal,[],[f483])).
% 2.08/0.68  fof(f483,plain,(
% 2.08/0.68    ( ! [X0] : (sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 2.08/0.68    inference(resolution,[],[f442,f160])).
% 2.08/0.68  fof(f160,plain,(
% 2.08/0.68    ( ! [X0] : (m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 2.08/0.68    inference(resolution,[],[f130,f66])).
% 2.08/0.68  fof(f66,plain,(
% 2.08/0.68    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.08/0.68    inference(cnf_transformation,[],[f44])).
% 2.08/0.68  fof(f44,plain,(
% 2.08/0.68    ! [X0,X1] : ((sK4(X0,X1) != X1 & r2_hidden(sK4(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.08/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f43])).
% 2.08/0.68  fof(f43,plain,(
% 2.08/0.68    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK4(X0,X1) != X1 & r2_hidden(sK4(X0,X1),X0)))),
% 2.08/0.68    introduced(choice_axiom,[])).
% 2.08/0.68  fof(f24,plain,(
% 2.08/0.68    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.08/0.68    inference(ennf_transformation,[],[f7])).
% 2.08/0.68  fof(f7,axiom,(
% 2.08/0.68    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 2.08/0.68  fof(f130,plain,(
% 2.08/0.68    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))) )),
% 2.08/0.68    inference(resolution,[],[f113,f46])).
% 2.08/0.68  fof(f46,plain,(
% 2.08/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.08/0.68    inference(cnf_transformation,[],[f37])).
% 2.08/0.68  fof(f113,plain,(
% 2.08/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k5_partfun1(X1,X2,sK2)) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.08/0.68    inference(resolution,[],[f73,f45])).
% 2.08/0.68  fof(f45,plain,(
% 2.08/0.68    v1_funct_1(sK2)),
% 2.08/0.68    inference(cnf_transformation,[],[f37])).
% 2.08/0.68  fof(f73,plain,(
% 2.08/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.08/0.68    inference(cnf_transformation,[],[f28])).
% 2.08/0.68  fof(f28,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.08/0.68    inference(flattening,[],[f27])).
% 2.08/0.68  fof(f27,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.08/0.68    inference(ennf_transformation,[],[f16])).
% 2.08/0.68  fof(f16,axiom,(
% 2.08/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 2.08/0.68  fof(f442,plain,(
% 2.08/0.68    ( ! [X0,X1] : (~m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1)) )),
% 2.08/0.68    inference(subsumption_resolution,[],[f441,f110])).
% 2.08/0.68  fof(f110,plain,(
% 2.08/0.68    v1_partfun1(sK3,sK0) | k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(subsumption_resolution,[],[f109,f47])).
% 2.08/0.68  fof(f47,plain,(
% 2.08/0.68    v1_funct_1(sK3)),
% 2.08/0.68    inference(cnf_transformation,[],[f37])).
% 2.08/0.68  fof(f109,plain,(
% 2.08/0.68    k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3)),
% 2.08/0.68    inference(subsumption_resolution,[],[f108,f49])).
% 2.08/0.68  fof(f108,plain,(
% 2.08/0.68    k1_xboole_0 = k1_tarski(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3)),
% 2.08/0.68    inference(resolution,[],[f84,f48])).
% 2.08/0.68  fof(f48,plain,(
% 2.08/0.68    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 2.08/0.68    inference(cnf_transformation,[],[f37])).
% 2.08/0.68  fof(f84,plain,(
% 2.08/0.68    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0) | ~v1_funct_1(X2)) )),
% 2.08/0.68    inference(duplicate_literal_removal,[],[f69])).
% 2.08/0.68  fof(f69,plain,(
% 2.08/0.68    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f26])).
% 2.08/0.68  fof(f26,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.08/0.68    inference(flattening,[],[f25])).
% 2.08/0.68  fof(f25,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.08/0.68    inference(ennf_transformation,[],[f12])).
% 2.08/0.68  fof(f12,axiom,(
% 2.08/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 2.08/0.68  fof(f441,plain,(
% 2.08/0.68    ( ! [X0,X1] : (k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0) | ~v1_partfun1(sK3,sK0) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | k1_xboole_0 = k1_tarski(sK1)) )),
% 2.08/0.68    inference(duplicate_literal_removal,[],[f440])).
% 2.08/0.68  fof(f440,plain,(
% 2.08/0.68    ( ! [X0,X1] : (k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0) | ~v1_partfun1(sK3,sK0) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 2.08/0.68    inference(resolution,[],[f291,f209])).
% 2.08/0.68  fof(f209,plain,(
% 2.08/0.68    ( ! [X0] : (v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 2.08/0.68    inference(subsumption_resolution,[],[f208,f160])).
% 2.08/0.68  fof(f208,plain,(
% 2.08/0.68    ( ! [X0] : (k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1) | ~m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0)) )),
% 2.08/0.68    inference(subsumption_resolution,[],[f207,f123])).
% 2.08/0.68  fof(f123,plain,(
% 2.08/0.68    ( ! [X0] : (v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 2.08/0.68    inference(resolution,[],[f117,f66])).
% 2.08/0.68  fof(f117,plain,(
% 2.08/0.68    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_1(X0)) )),
% 2.08/0.68    inference(resolution,[],[f104,f46])).
% 2.08/0.68  fof(f104,plain,(
% 2.08/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k5_partfun1(X1,X2,sK2)) | v1_funct_1(X0)) )),
% 2.08/0.68    inference(resolution,[],[f71,f45])).
% 2.08/0.68  fof(f71,plain,(
% 2.08/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(X3)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f28])).
% 2.08/0.68  fof(f207,plain,(
% 2.08/0.68    ( ! [X0] : (k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1) | ~m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0) | ~v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))) )),
% 2.08/0.68    inference(resolution,[],[f158,f84])).
% 2.08/0.68  fof(f158,plain,(
% 2.08/0.68    ( ! [X0] : (v1_funct_2(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 2.08/0.68    inference(resolution,[],[f124,f66])).
% 2.08/0.68  fof(f124,plain,(
% 2.08/0.68    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_2(X0,sK0,k1_tarski(sK1))) )),
% 2.08/0.68    inference(resolution,[],[f106,f46])).
% 2.08/0.68  fof(f106,plain,(
% 2.08/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k5_partfun1(X1,X2,sK2)) | v1_funct_2(X0,X1,X2)) )),
% 2.08/0.68    inference(resolution,[],[f72,f45])).
% 2.08/0.68  fof(f72,plain,(
% 2.08/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X3,X0,X1)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f28])).
% 2.08/0.68  fof(f291,plain,(
% 2.08/0.68    ( ! [X4,X5,X3] : (~v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),X4) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3) | ~v1_partfun1(sK3,X4) | k1_tarski(X3) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 2.08/0.68    inference(subsumption_resolution,[],[f290,f123])).
% 2.08/0.68  fof(f290,plain,(
% 2.08/0.68    ( ! [X4,X5,X3] : (k1_tarski(X3) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3) | ~v1_partfun1(sK3,X4) | ~v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),X4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3))) )),
% 2.08/0.68    inference(subsumption_resolution,[],[f286,f47])).
% 2.08/0.68  fof(f286,plain,(
% 2.08/0.68    ( ! [X4,X5,X3] : (k1_tarski(X3) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3) | ~v1_partfun1(sK3,X4) | ~v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),X4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X3))) )),
% 2.08/0.68    inference(resolution,[],[f253,f76])).
% 2.08/0.68  fof(f76,plain,(
% 2.08/0.68    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f32])).
% 2.08/0.68  fof(f32,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.08/0.68    inference(flattening,[],[f31])).
% 2.08/0.68  fof(f31,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.08/0.68    inference(ennf_transformation,[],[f14])).
% 2.08/0.68  fof(f14,axiom,(
% 2.08/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 2.08/0.68  fof(f253,plain,(
% 2.08/0.68    ( ! [X0] : (r1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK3) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 2.08/0.68    inference(subsumption_resolution,[],[f252,f49])).
% 2.08/0.68  fof(f252,plain,(
% 2.08/0.68    ( ! [X0] : (k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | r1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK3) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))) )),
% 2.08/0.68    inference(duplicate_literal_removal,[],[f250])).
% 2.08/0.68  fof(f250,plain,(
% 2.08/0.68    ( ! [X0] : (k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | r1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK3) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 2.08/0.68    inference(resolution,[],[f195,f160])).
% 2.08/0.68  fof(f195,plain,(
% 2.08/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | r1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK3) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))) )),
% 2.08/0.68    inference(resolution,[],[f123,f116])).
% 2.08/0.68  fof(f116,plain,(
% 2.08/0.68    ( ! [X4,X5,X3] : (~v1_funct_1(X5) | r1_partfun1(X5,sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,k1_tarski(X4)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,k1_tarski(X4))))) )),
% 2.08/0.68    inference(resolution,[],[f77,f47])).
% 2.08/0.68  fof(f77,plain,(
% 2.08/0.68    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r1_partfun1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f34])).
% 2.08/0.68  fof(f34,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 2.08/0.68    inference(flattening,[],[f33])).
% 2.08/0.68  fof(f33,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 2.08/0.68    inference(ennf_transformation,[],[f13])).
% 2.08/0.68  fof(f13,axiom,(
% 2.08/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).
% 2.08/0.68  fof(f67,plain,(
% 2.08/0.68    ( ! [X0,X1] : (sK4(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.08/0.68    inference(cnf_transformation,[],[f44])).
% 2.08/0.68  fof(f332,plain,(
% 2.08/0.68    ~r1_tarski(k5_partfun1(sK0,k1_tarski(sK1),sK2),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(subsumption_resolution,[],[f330,f50])).
% 2.08/0.68  fof(f330,plain,(
% 2.08/0.68    k1_xboole_0 = k1_tarski(sK1) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | ~r1_tarski(k5_partfun1(sK0,k1_tarski(sK1),sK2),k1_tarski(sK3))),
% 2.08/0.68    inference(resolution,[],[f329,f60])).
% 2.08/0.68  fof(f60,plain,(
% 2.08/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f39])).
% 2.08/0.68  fof(f39,plain,(
% 2.08/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.68    inference(flattening,[],[f38])).
% 2.08/0.68  fof(f38,plain,(
% 2.08/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.68    inference(nnf_transformation,[],[f1])).
% 2.08/0.68  fof(f1,axiom,(
% 2.08/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.08/0.68  fof(f329,plain,(
% 2.08/0.68    r1_tarski(k1_tarski(sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2)) | k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(resolution,[],[f249,f61])).
% 2.08/0.68  fof(f61,plain,(
% 2.08/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f40])).
% 2.08/0.68  fof(f40,plain,(
% 2.08/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.08/0.68    inference(nnf_transformation,[],[f11])).
% 2.08/0.68  fof(f11,axiom,(
% 2.08/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.08/0.68  fof(f249,plain,(
% 2.08/0.68    m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(k5_partfun1(sK0,k1_tarski(sK1),sK2))) | k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(resolution,[],[f221,f57])).
% 2.08/0.68  fof(f57,plain,(
% 2.08/0.68    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 2.08/0.68    inference(cnf_transformation,[],[f23])).
% 2.08/0.68  fof(f23,plain,(
% 2.08/0.68    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.08/0.68    inference(ennf_transformation,[],[f10])).
% 2.08/0.68  fof(f10,axiom,(
% 2.08/0.68    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 2.08/0.68  fof(f221,plain,(
% 2.08/0.68    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | k1_xboole_0 = k1_tarski(sK1)),
% 2.08/0.68    inference(subsumption_resolution,[],[f220,f46])).
% 2.08/0.68  fof(f220,plain,(
% 2.08/0.68    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | k1_xboole_0 = k1_tarski(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.08/0.68    inference(subsumption_resolution,[],[f219,f49])).
% 2.08/0.68  fof(f219,plain,(
% 2.08/0.68    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k1_tarski(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.08/0.68    inference(resolution,[],[f192,f48])).
% 2.08/0.68  fof(f192,plain,(
% 2.08/0.68    ( ! [X0,X1] : (~v1_funct_2(sK3,X1,X0) | r2_hidden(sK3,k5_partfun1(X1,X0,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.08/0.68    inference(subsumption_resolution,[],[f191,f45])).
% 2.08/0.68  fof(f191,plain,(
% 2.08/0.68    ( ! [X0,X1] : (k1_xboole_0 = X0 | r2_hidden(sK3,k5_partfun1(X1,X0,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(sK2)) )),
% 2.08/0.68    inference(subsumption_resolution,[],[f188,f47])).
% 2.08/0.68  fof(f188,plain,(
% 2.08/0.68    ( ! [X0,X1] : (k1_xboole_0 = X0 | r2_hidden(sK3,k5_partfun1(X1,X0,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(sK2)) )),
% 2.08/0.68    inference(resolution,[],[f175,f74])).
% 2.08/0.68  fof(f74,plain,(
% 2.08/0.68    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | k1_xboole_0 = X1 | r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f30])).
% 2.08/0.68  fof(f30,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.08/0.68    inference(flattening,[],[f29])).
% 2.08/0.68  fof(f29,plain,(
% 2.08/0.68    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.08/0.68    inference(ennf_transformation,[],[f15])).
% 2.08/0.68  fof(f15,axiom,(
% 2.08/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).
% 2.08/0.68  fof(f175,plain,(
% 2.08/0.68    r1_partfun1(sK2,sK3)),
% 2.08/0.68    inference(subsumption_resolution,[],[f173,f46])).
% 2.08/0.68  fof(f173,plain,(
% 2.08/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r1_partfun1(sK2,sK3)),
% 2.08/0.68    inference(resolution,[],[f139,f49])).
% 2.08/0.68  fof(f139,plain,(
% 2.08/0.68    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r1_partfun1(sK2,sK3)) )),
% 2.08/0.68    inference(resolution,[],[f116,f45])).
% 2.08/0.68  fof(f55,plain,(
% 2.08/0.68    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 2.08/0.68    inference(cnf_transformation,[],[f22])).
% 2.08/0.68  fof(f22,plain,(
% 2.08/0.68    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 2.08/0.68    inference(ennf_transformation,[],[f9])).
% 2.08/0.68  fof(f9,axiom,(
% 2.08/0.68    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 2.08/0.68  fof(f2206,plain,(
% 2.08/0.68    k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)),
% 2.08/0.68    inference(backward_demodulation,[],[f924,f2141])).
% 2.08/0.68  fof(f924,plain,(
% 2.08/0.68    k5_partfun1(sK0,k1_xboole_0,k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 2.08/0.68    inference(backward_demodulation,[],[f850,f903])).
% 2.08/0.68  fof(f903,plain,(
% 2.08/0.68    k1_xboole_0 = sK3),
% 2.08/0.68    inference(subsumption_resolution,[],[f902,f51])).
% 2.08/0.68  fof(f902,plain,(
% 2.08/0.68    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3),
% 2.08/0.68    inference(forward_demodulation,[],[f901,f80])).
% 2.08/0.68  fof(f80,plain,(
% 2.08/0.68    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.08/0.68    inference(equality_resolution,[],[f65])).
% 2.08/0.68  fof(f65,plain,(
% 2.08/0.68    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.08/0.68    inference(cnf_transformation,[],[f42])).
% 2.08/0.68  fof(f901,plain,(
% 2.08/0.68    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | k1_xboole_0 = sK3),
% 2.08/0.68    inference(forward_demodulation,[],[f900,f685])).
% 2.08/0.68  fof(f900,plain,(
% 2.08/0.68    k1_xboole_0 = sK3 | ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3)),
% 2.08/0.68    inference(forward_demodulation,[],[f693,f80])).
% 2.08/0.68  fof(f693,plain,(
% 2.08/0.68    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3)),
% 2.08/0.68    inference(backward_demodulation,[],[f111,f685])).
% 2.08/0.68  fof(f111,plain,(
% 2.08/0.68    ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK3) | k2_zfmisc_1(sK0,k1_tarski(sK1)) = sK3),
% 2.08/0.68    inference(resolution,[],[f92,f60])).
% 2.08/0.68  fof(f92,plain,(
% 2.08/0.68    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_tarski(sK1)))),
% 2.08/0.68    inference(resolution,[],[f61,f49])).
% 2.08/0.68  fof(f850,plain,(
% 2.08/0.68    k1_tarski(sK3) != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)),
% 2.08/0.68    inference(backward_demodulation,[],[f689,f825])).
% 2.08/0.68  fof(f825,plain,(
% 2.08/0.68    k1_xboole_0 = sK2),
% 2.08/0.68    inference(subsumption_resolution,[],[f824,f51])).
% 2.08/0.68  fof(f824,plain,(
% 2.08/0.68    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 2.08/0.68    inference(forward_demodulation,[],[f823,f80])).
% 2.08/0.68  fof(f823,plain,(
% 2.08/0.68    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | k1_xboole_0 = sK2),
% 2.08/0.68    inference(forward_demodulation,[],[f822,f685])).
% 2.08/0.68  fof(f822,plain,(
% 2.08/0.68    k1_xboole_0 = sK2 | ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)),
% 2.08/0.68    inference(forward_demodulation,[],[f692,f80])).
% 2.08/0.68  fof(f692,plain,(
% 2.08/0.68    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2)),
% 2.08/0.68    inference(backward_demodulation,[],[f99,f685])).
% 2.08/0.68  fof(f99,plain,(
% 2.08/0.68    ~r1_tarski(k2_zfmisc_1(sK0,k1_tarski(sK1)),sK2) | sK2 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 2.08/0.68    inference(resolution,[],[f91,f60])).
% 2.08/0.68  fof(f91,plain,(
% 2.08/0.68    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_tarski(sK1)))),
% 2.08/0.68    inference(resolution,[],[f61,f46])).
% 2.08/0.68  fof(f689,plain,(
% 2.08/0.68    k1_tarski(sK3) != k5_partfun1(sK0,k1_xboole_0,sK2)),
% 2.08/0.68    inference(backward_demodulation,[],[f50,f685])).
% 2.08/0.68  % SZS output end Proof for theBenchmark
% 2.08/0.68  % (11309)------------------------------
% 2.08/0.68  % (11309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.68  % (11309)Termination reason: Refutation
% 2.08/0.68  
% 2.08/0.68  % (11309)Memory used [KB]: 2558
% 2.08/0.68  % (11309)Time elapsed: 0.220 s
% 2.08/0.68  % (11309)------------------------------
% 2.08/0.68  % (11309)------------------------------
% 2.08/0.68  % (11296)Success in time 0.316 s
%------------------------------------------------------------------------------
