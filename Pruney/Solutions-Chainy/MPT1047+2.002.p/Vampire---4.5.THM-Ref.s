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
% DateTime   : Thu Dec  3 13:07:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  170 (21407 expanded)
%              Number of leaves         :   23 (6636 expanded)
%              Depth                    :   33
%              Number of atoms          :  675 (124974 expanded)
%              Number of equality atoms :  177 (25000 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1062,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1031,f1021])).

fof(f1021,plain,(
    ! [X2,X1] : X1 = X2 ),
    inference(subsumption_resolution,[],[f1019,f1014])).

fof(f1014,plain,(
    ! [X0,X1] : r1_tarski(X0,X1) ),
    inference(resolution,[],[f992,f914])).

fof(f914,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f103,f890])).

fof(f890,plain,(
    ! [X6] : k1_xboole_0 = X6 ),
    inference(subsumption_resolution,[],[f884,f111])).

fof(f111,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f884,plain,(
    ! [X6] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X6)
      | k1_xboole_0 = X6 ) ),
    inference(superposition,[],[f75,f413])).

fof(f413,plain,(
    k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f401,f108])).

fof(f108,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f401,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK5))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(backward_demodulation,[],[f287,f383])).

fof(f383,plain,(
    k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) ),
    inference(subsumption_resolution,[],[f382,f66])).

fof(f66,plain,(
    k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
          & v1_funct_2(X3,sK2,k1_tarski(sK3))
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
        & v1_funct_2(X3,sK2,k1_tarski(sK3))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f18])).

% (26436)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f382,plain,
    ( k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
    | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5) ),
    inference(equality_resolution,[],[f375])).

fof(f375,plain,(
    ! [X4] :
      ( sK5 != X4
      | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X4) ) ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,(
    ! [X4] :
      ( sK5 != X4
      | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X4)
      | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X4)
      | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) ) ),
    inference(superposition,[],[f68,f321])).

fof(f321,plain,(
    ! [X2] :
      ( sK5 = sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X2)
      | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X2)
      | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) ) ),
    inference(subsumption_resolution,[],[f302,f320])).

fof(f320,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | r2_relset_1(sK2,k1_tarski(sK3),sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK5) ) ),
    inference(subsumption_resolution,[],[f319,f179])).

fof(f179,plain,(
    ! [X0] :
      ( v1_funct_2(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X0),sK2,k1_tarski(sK3))
      | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4) ) ),
    inference(resolution,[],[f137,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK6(X0,X1) != X1
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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

fof(f137,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | v1_funct_2(X3,sK2,k1_tarski(sK3)) ) ),
    inference(subsumption_resolution,[],[f126,f61])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f126,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | v1_funct_2(X3,sK2,k1_tarski(sK3))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f62,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2) ) ),
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

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f319,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | r2_relset_1(sK2,k1_tarski(sK3),sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK5)
      | ~ v1_funct_2(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK2,k1_tarski(sK3)) ) ),
    inference(subsumption_resolution,[],[f301,f166])).

fof(f166,plain,(
    ! [X0] :
      ( v1_funct_1(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X0))
      | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4) ) ),
    inference(resolution,[],[f136,f67])).

fof(f136,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f125,f61])).

fof(f125,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | v1_funct_1(X2)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f62,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f301,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | r2_relset_1(sK2,k1_tarski(sK3),sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK5)
      | ~ v1_funct_2(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK2,k1_tarski(sK3))
      | ~ v1_funct_1(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1)) ) ),
    inference(resolution,[],[f194,f155])).

fof(f155,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | r2_relset_1(sK2,k1_tarski(sK3),X1,sK5)
      | ~ v1_funct_2(X1,sK2,k1_tarski(sK3))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f154,f63])).

fof(f63,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f154,plain,(
    ! [X1] :
      ( r2_relset_1(sK2,k1_tarski(sK3),X1,sK5)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | ~ v1_funct_2(X1,sK2,k1_tarski(sK3))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f143,f64])).

fof(f64,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f143,plain,(
    ! [X1] :
      ( r2_relset_1(sK2,k1_tarski(sK3),X1,sK5)
      | ~ v1_funct_2(sK5,sK2,k1_tarski(sK3))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | ~ v1_funct_2(X1,sK2,k1_tarski(sK3))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f65,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f194,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X0),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4) ) ),
    inference(resolution,[],[f138,f67])).

fof(f138,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ) ),
    inference(subsumption_resolution,[],[f127,f61])).

fof(f127,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f62,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f302,plain,(
    ! [X2] :
      ( k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X2)
      | sK5 = sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X2)
      | ~ r2_relset_1(sK2,k1_tarski(sK3),sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X2),sK5) ) ),
    inference(resolution,[],[f194,f148])).

fof(f148,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | sK5 = X5
      | ~ r2_relset_1(sK2,k1_tarski(sK3),X5,sK5) ) ),
    inference(resolution,[],[f65,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f287,plain,
    ( ~ r1_tarski(k5_partfun1(sK2,k1_tarski(sK3),sK4),k1_tarski(sK5))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f286,f66])).

fof(f286,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5)
    | ~ r1_tarski(k5_partfun1(sK2,k1_tarski(sK3),sK4),k1_tarski(sK5)) ),
    inference(resolution,[],[f285,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f285,plain,
    ( r1_tarski(k1_tarski(sK5),k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(forward_demodulation,[],[f284,f78])).

fof(f78,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f284,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k1_xboole_0 = k1_tarski(sK3)
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(resolution,[],[f251,f241])).

fof(f241,plain,
    ( r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(resolution,[],[f211,f162])).

fof(f162,plain,
    ( v1_partfun1(sK5,sK2)
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f161,f63])).

fof(f161,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | v1_partfun1(sK5,sK2)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f150,f64])).

fof(f150,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | v1_partfun1(sK5,sK2)
    | ~ v1_funct_2(sK5,sK2,k1_tarski(sK3))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f65,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f211,plain,
    ( ~ v1_partfun1(sK5,sK2)
    | r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f209,f188])).

fof(f188,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f183,f61])).

fof(f183,plain,
    ( r1_partfun1(sK4,sK5)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f153,f62])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | r1_partfun1(X0,sK5)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f142,f63])).

fof(f142,plain,(
    ! [X0] :
      ( r1_partfun1(X0,sK5)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f65,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

% (26446)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f209,plain,
    ( ~ v1_partfun1(sK5,sK2)
    | r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | ~ r1_partfun1(sK4,sK5) ),
    inference(resolution,[],[f160,f141])).

fof(f141,plain,(
    sP0(sK4,sK2,k1_tarski(sK3),k5_partfun1(sK2,k1_tarski(sK3),sK4)) ),
    inference(resolution,[],[f135,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f135,plain,(
    sP1(k1_tarski(sK3),sK2,sK4) ),
    inference(subsumption_resolution,[],[f124,f61])).

fof(f124,plain,
    ( sP1(k1_tarski(sK3),sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f62,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X1,X0,X2)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f26,f38,f37])).

fof(f37,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(f160,plain,(
    ! [X6,X7] :
      ( ~ sP0(X6,sK2,k1_tarski(sK3),X7)
      | ~ v1_partfun1(sK5,sK2)
      | r2_hidden(sK5,X7)
      | ~ r1_partfun1(X6,sK5) ) ),
    inference(subsumption_resolution,[],[f149,f63])).

fof(f149,plain,(
    ! [X6,X7] :
      ( ~ r1_partfun1(X6,sK5)
      | ~ v1_partfun1(sK5,sK2)
      | r2_hidden(sK5,X7)
      | ~ v1_funct_1(sK5)
      | ~ sP0(X6,sK2,k1_tarski(sK3),X7) ) ),
    inference(resolution,[],[f65,f116])).

fof(f116,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | r2_hidden(X8,X3)
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK7(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK8(X0,X1,X2,X3))
              & v1_partfun1(sK8(X0,X1,X2,X3),X1)
              & sK7(X0,X1,X2,X3) = sK8(X0,X1,X2,X3)
              & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK8(X0,X1,X2,X3)) )
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK9(X0,X1,X2,X7))
                & v1_partfun1(sK9(X0,X1,X2,X7),X1)
                & sK9(X0,X1,X2,X7) = X7
                & m1_subset_1(sK9(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK9(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f52,f55,f54,f53])).

fof(f53,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK7(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK7(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & sK7(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK8(X0,X1,X2,X3))
        & v1_partfun1(sK8(X0,X1,X2,X3),X1)
        & sK7(X0,X1,X2,X3) = sK8(X0,X1,X2,X3)
        & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK8(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK9(X0,X1,X2,X7))
        & v1_partfun1(sK9(X0,X1,X2,X7),X1)
        & sK9(X0,X1,X2,X7) = X7
        & m1_subset_1(sK9(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK9(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | r1_tarski(k2_tarski(X0,sK5),k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | k1_xboole_0 = k1_tarski(sK3) ) ),
    inference(resolution,[],[f241,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

% (26453)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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

fof(f992,plain,(
    ! [X4] : m1_subset_1(X4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f921,f957])).

fof(f957,plain,(
    ! [X2,X0] : r2_hidden(X0,X2) ),
    inference(subsumption_resolution,[],[f892,f108])).

fof(f892,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | r2_hidden(X0,X2) ) ),
    inference(backward_demodulation,[],[f105,f890])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f921,plain,(
    ! [X4] :
      ( m1_subset_1(X4,k1_xboole_0)
      | ~ r2_hidden(X4,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f856,f890])).

fof(f856,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f565,f852])).

fof(f852,plain,(
    k1_xboole_0 = k5_partfun1(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f493,f524])).

fof(f524,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f523,f108])).

fof(f523,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f522,f110])).

fof(f110,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f522,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_xboole_0),sK4)
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f521,f413])).

fof(f521,plain,
    ( k1_xboole_0 = sK4
    | ~ r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK4) ),
    inference(forward_demodulation,[],[f436,f110])).

fof(f436,plain,
    ( sK4 = k2_zfmisc_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK4) ),
    inference(backward_demodulation,[],[f164,f413])).

fof(f164,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK4)
    | sK4 = k2_zfmisc_1(sK2,k1_tarski(sK3)) ),
    inference(resolution,[],[f132,f74])).

fof(f132,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(resolution,[],[f62,f103])).

fof(f493,plain,(
    k1_xboole_0 = k5_partfun1(sK2,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f383,f413])).

fof(f565,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_partfun1(sK2,k1_xboole_0,k1_xboole_0))
      | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f520,f547])).

fof(f547,plain,(
    k1_xboole_0 = sK5 ),
    inference(subsumption_resolution,[],[f546,f108])).

fof(f546,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(forward_demodulation,[],[f545,f110])).

fof(f545,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_xboole_0),sK5)
    | k1_xboole_0 = sK5 ),
    inference(forward_demodulation,[],[f544,f413])).

fof(f544,plain,
    ( k1_xboole_0 = sK5
    | ~ r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK5) ),
    inference(forward_demodulation,[],[f437,f110])).

fof(f437,plain,
    ( sK5 = k2_zfmisc_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK5) ),
    inference(backward_demodulation,[],[f165,f413])).

fof(f165,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK5)
    | k2_zfmisc_1(sK2,k1_tarski(sK3)) = sK5 ),
    inference(resolution,[],[f152,f74])).

fof(f152,plain,(
    r1_tarski(sK5,k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(resolution,[],[f65,f103])).

fof(f520,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_partfun1(sK2,k1_xboole_0,sK5))
      | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f519,f413])).

fof(f519,plain,(
    ! [X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK5)) ) ),
    inference(forward_demodulation,[],[f433,f110])).

fof(f433,plain,(
    ! [X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
      | ~ r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK5)) ) ),
    inference(backward_demodulation,[],[f159,f413])).

fof(f159,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK5))
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ) ),
    inference(subsumption_resolution,[],[f147,f63])).

fof(f147,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK5))
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f65,f96])).

fof(f1019,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f1014,f74])).

fof(f1031,plain,(
    ! [X0] : k1_tarski(X0) != X0 ),
    inference(superposition,[],[f551,f1021])).

fof(f551,plain,(
    k1_xboole_0 != k1_tarski(k1_xboole_0) ),
    inference(backward_demodulation,[],[f384,f547])).

fof(f384,plain,(
    k1_xboole_0 != k1_tarski(sK5) ),
    inference(backward_demodulation,[],[f66,f383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (26430)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.48  % (26423)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (26445)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (26437)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (26429)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (26428)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (26431)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (26427)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (26426)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (26424)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (26440)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (26441)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (26442)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (26449)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (26444)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (26435)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (26433)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (26434)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (26448)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (26452)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (26450)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (26437)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f1062,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f1031,f1021])).
% 0.21/0.55  fof(f1021,plain,(
% 0.21/0.55    ( ! [X2,X1] : (X1 = X2) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f1019,f1014])).
% 0.21/0.55  fof(f1014,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f992,f914])).
% 0.21/0.55  fof(f914,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_xboole_0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(backward_demodulation,[],[f103,f890])).
% 0.21/0.55  fof(f890,plain,(
% 0.21/0.55    ( ! [X6] : (k1_xboole_0 = X6) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f884,f111])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.55    inference(flattening,[],[f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.55  fof(f884,plain,(
% 0.21/0.55    ( ! [X6] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X6) | k1_xboole_0 = X6) )),
% 0.21/0.55    inference(superposition,[],[f75,f413])).
% 0.21/0.55  fof(f413,plain,(
% 0.21/0.55    k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f401,f108])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f401,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k1_tarski(sK5)) | k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.55    inference(backward_demodulation,[],[f287,f383])).
% 0.21/0.55  fof(f383,plain,(
% 0.21/0.55    k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f382,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5)),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    (k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_1(sK4)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f41,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(X3,sK2,k1_tarski(sK3)) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_1(sK4))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(X3,sK2,k1_tarski(sK3)) & v1_funct_1(X3)) => (k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 0.21/0.55    inference(negated_conjecture,[],[f18])).
% 0.21/0.55  % (26436)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  fof(f18,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).
% 0.21/0.55  fof(f382,plain,(
% 0.21/0.55    k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5)),
% 0.21/0.55    inference(equality_resolution,[],[f375])).
% 0.21/0.55  fof(f375,plain,(
% 0.21/0.55    ( ! [X4] : (sK5 != X4 | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X4)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f374])).
% 0.21/0.55  fof(f374,plain,(
% 0.21/0.55    ( ! [X4] : (sK5 != X4 | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X4) | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X4) | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)) )),
% 0.21/0.55    inference(superposition,[],[f68,f321])).
% 0.21/0.55  fof(f321,plain,(
% 0.21/0.55    ( ! [X2] : (sK5 = sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X2) | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X2) | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f302,f320])).
% 0.21/0.55  fof(f320,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4) | r2_relset_1(sK2,k1_tarski(sK3),sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK5)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f319,f179])).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_2(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X0),sK2,k1_tarski(sK3)) | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4)) )),
% 0.21/0.55    inference(resolution,[],[f137,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ! [X0,X1] : ((sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK6(X0,X1) != X1 & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | v1_funct_2(X3,sK2,k1_tarski(sK3))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f126,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    v1_funct_1(sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | v1_funct_2(X3,sK2,k1_tarski(sK3)) | ~v1_funct_1(sK4)) )),
% 0.21/0.55    inference(resolution,[],[f62,f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f319,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4) | r2_relset_1(sK2,k1_tarski(sK3),sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK5) | ~v1_funct_2(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK2,k1_tarski(sK3))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f301,f166])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_1(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X0)) | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4)) )),
% 0.21/0.55    inference(resolution,[],[f136,f67])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | v1_funct_1(X2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f125,f61])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | v1_funct_1(X2) | ~v1_funct_1(sK4)) )),
% 0.21/0.55    inference(resolution,[],[f62,f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3) | ~v1_funct_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f301,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4) | r2_relset_1(sK2,k1_tarski(sK3),sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK5) | ~v1_funct_2(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1),sK2,k1_tarski(sK3)) | ~v1_funct_1(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X1))) )),
% 0.21/0.55    inference(resolution,[],[f194,f155])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | r2_relset_1(sK2,k1_tarski(sK3),X1,sK5) | ~v1_funct_2(X1,sK2,k1_tarski(sK3)) | ~v1_funct_1(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f154,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    v1_funct_1(sK5)),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    ( ! [X1] : (r2_relset_1(sK2,k1_tarski(sK3),X1,sK5) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | ~v1_funct_2(X1,sK2,k1_tarski(sK3)) | ~v1_funct_1(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f143,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    ( ! [X1] : (r2_relset_1(sK2,k1_tarski(sK3),X1,sK5) | ~v1_funct_2(sK5,sK2,k1_tarski(sK3)) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | ~v1_funct_2(X1,sK2,k1_tarski(sK3)) | ~v1_funct_1(X1)) )),
% 0.21/0.55    inference(resolution,[],[f65,f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r2_relset_1(X0,k1_tarski(X1),X2,X3) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X0),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4)) )),
% 0.21/0.55    inference(resolution,[],[f138,f67])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f127,f61])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | ~v1_funct_1(sK4)) )),
% 0.21/0.55    inference(resolution,[],[f62,f96])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f302,plain,(
% 0.21/0.55    ( ! [X2] : (k1_xboole_0 = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(X2) | sK5 = sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X2) | ~r2_relset_1(sK2,k1_tarski(sK3),sK6(k5_partfun1(sK2,k1_tarski(sK3),sK4),X2),sK5)) )),
% 0.21/0.55    inference(resolution,[],[f194,f148])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | sK5 = X5 | ~r2_relset_1(sK2,k1_tarski(sK3),X5,sK5)) )),
% 0.21/0.55    inference(resolution,[],[f65,f100])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(flattening,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sK6(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    ~r1_tarski(k5_partfun1(sK2,k1_tarski(sK3),sK4),k1_tarski(sK5)) | k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f286,f66])).
% 0.21/0.55  fof(f286,plain,(
% 0.21/0.55    k1_xboole_0 = k1_tarski(sK3) | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5) | ~r1_tarski(k5_partfun1(sK2,k1_tarski(sK3),sK4),k1_tarski(sK5))),
% 0.21/0.55    inference(resolution,[],[f285,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f285,plain,(
% 0.21/0.55    r1_tarski(k1_tarski(sK5),k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.55    inference(forward_demodulation,[],[f284,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f284,plain,(
% 0.21/0.55    r1_tarski(k2_tarski(sK5,sK5),k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f283])).
% 0.21/0.55  fof(f283,plain,(
% 0.21/0.55    r1_tarski(k2_tarski(sK5,sK5),k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3) | k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.55    inference(resolution,[],[f251,f241])).
% 0.21/0.55  fof(f241,plain,(
% 0.21/0.55    r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.55    inference(resolution,[],[f211,f162])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    v1_partfun1(sK5,sK2) | k1_xboole_0 = k1_tarski(sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f161,f63])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    k1_xboole_0 = k1_tarski(sK3) | v1_partfun1(sK5,sK2) | ~v1_funct_1(sK5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f150,f64])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    k1_xboole_0 = k1_tarski(sK3) | v1_partfun1(sK5,sK2) | ~v1_funct_2(sK5,sK2,k1_tarski(sK3)) | ~v1_funct_1(sK5)),
% 0.21/0.55    inference(resolution,[],[f65,f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f97])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    ~v1_partfun1(sK5,sK2) | r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f209,f188])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    r1_partfun1(sK4,sK5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f183,f61])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    r1_partfun1(sK4,sK5) | ~v1_funct_1(sK4)),
% 0.21/0.55    inference(resolution,[],[f153,f62])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | r1_partfun1(X0,sK5) | ~v1_funct_1(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f142,f63])).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    ( ! [X0] : (r1_partfun1(X0,sK5) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | ~v1_funct_1(X0)) )),
% 0.21/0.55    inference(resolution,[],[f65,f102])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r1_partfun1(X2,X3) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  % (26446)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).
% 0.21/0.55  fof(f209,plain,(
% 0.21/0.55    ~v1_partfun1(sK5,sK2) | r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | ~r1_partfun1(sK4,sK5)),
% 0.21/0.55    inference(resolution,[],[f160,f141])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    sP0(sK4,sK2,k1_tarski(sK3),k5_partfun1(sK2,k1_tarski(sK3),sK4))),
% 0.21/0.55    inference(resolution,[],[f135,f114])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))) )),
% 0.21/0.55    inference(equality_resolution,[],[f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 0.21/0.55    inference(rectify,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    sP1(k1_tarski(sK3),sK2,sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f124,f61])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    sP1(k1_tarski(sK3),sK2,sK4) | ~v1_funct_1(sK4)),
% 0.21/0.55    inference(resolution,[],[f62,f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X1,X0,X2) | ~v1_funct_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.55    inference(definition_folding,[],[f26,f38,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    ( ! [X6,X7] : (~sP0(X6,sK2,k1_tarski(sK3),X7) | ~v1_partfun1(sK5,sK2) | r2_hidden(sK5,X7) | ~r1_partfun1(X6,sK5)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f149,f63])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    ( ! [X6,X7] : (~r1_partfun1(X6,sK5) | ~v1_partfun1(sK5,sK2) | r2_hidden(sK5,X7) | ~v1_funct_1(sK5) | ~sP0(X6,sK2,k1_tarski(sK3),X7)) )),
% 0.21/0.55    inference(resolution,[],[f65,f116])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    ( ! [X2,X0,X8,X3,X1] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | r2_hidden(X8,X3) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.55    inference(equality_resolution,[],[f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK7(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK8(X0,X1,X2,X3)) & v1_partfun1(sK8(X0,X1,X2,X3),X1) & sK7(X0,X1,X2,X3) = sK8(X0,X1,X2,X3) & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK8(X0,X1,X2,X3))) | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK9(X0,X1,X2,X7)) & v1_partfun1(sK9(X0,X1,X2,X7),X1) & sK9(X0,X1,X2,X7) = X7 & m1_subset_1(sK9(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK9(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f52,f55,f54,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK7(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK7(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK7(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK8(X0,X1,X2,X3)) & v1_partfun1(sK8(X0,X1,X2,X3),X1) & sK7(X0,X1,X2,X3) = sK8(X0,X1,X2,X3) & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK8(X0,X1,X2,X3))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK9(X0,X1,X2,X7)) & v1_partfun1(sK9(X0,X1,X2,X7),X1) & sK9(X0,X1,X2,X7) = X7 & m1_subset_1(sK9(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK9(X0,X1,X2,X7))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.55    inference(rectify,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 0.21/0.55    inference(nnf_transformation,[],[f37])).
% 0.21/0.55  fof(f251,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | r1_tarski(k2_tarski(X0,sK5),k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3)) )),
% 0.21/0.55    inference(resolution,[],[f241,f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.55    inference(flattening,[],[f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.55    inference(nnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.55  % (26453)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f992,plain,(
% 0.21/0.55    ( ! [X4] : (m1_subset_1(X4,k1_xboole_0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f921,f957])).
% 0.21/0.55  fof(f957,plain,(
% 0.21/0.55    ( ! [X2,X0] : (r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f892,f108])).
% 0.21/0.55  fof(f892,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~r1_tarski(k1_xboole_0,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(backward_demodulation,[],[f105,f890])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f60])).
% 0.21/0.55  fof(f921,plain,(
% 0.21/0.55    ( ! [X4] : (m1_subset_1(X4,k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0)) )),
% 0.21/0.55    inference(backward_demodulation,[],[f856,f890])).
% 0.21/0.55  fof(f856,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.55    inference(backward_demodulation,[],[f565,f852])).
% 0.21/0.55  fof(f852,plain,(
% 0.21/0.55    k1_xboole_0 = k5_partfun1(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f493,f524])).
% 0.21/0.55  fof(f524,plain,(
% 0.21/0.55    k1_xboole_0 = sK4),
% 0.21/0.55    inference(subsumption_resolution,[],[f523,f108])).
% 0.21/0.55  fof(f523,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,sK4) | k1_xboole_0 = sK4),
% 0.21/0.55    inference(forward_demodulation,[],[f522,f110])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f522,plain,(
% 0.21/0.55    ~r1_tarski(k2_zfmisc_1(sK2,k1_xboole_0),sK4) | k1_xboole_0 = sK4),
% 0.21/0.55    inference(forward_demodulation,[],[f521,f413])).
% 0.21/0.55  fof(f521,plain,(
% 0.21/0.55    k1_xboole_0 = sK4 | ~r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK4)),
% 0.21/0.55    inference(forward_demodulation,[],[f436,f110])).
% 0.21/0.55  fof(f436,plain,(
% 0.21/0.55    sK4 = k2_zfmisc_1(sK2,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK4)),
% 0.21/0.55    inference(backward_demodulation,[],[f164,f413])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    ~r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK4) | sK4 = k2_zfmisc_1(sK2,k1_tarski(sK3))),
% 0.21/0.55    inference(resolution,[],[f132,f74])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    r1_tarski(sK4,k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.21/0.55    inference(resolution,[],[f62,f103])).
% 0.21/0.55  fof(f493,plain,(
% 0.21/0.55    k1_xboole_0 = k5_partfun1(sK2,k1_xboole_0,sK4)),
% 0.21/0.55    inference(backward_demodulation,[],[f383,f413])).
% 0.21/0.55  fof(f565,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k5_partfun1(sK2,k1_xboole_0,k1_xboole_0)) | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.55    inference(backward_demodulation,[],[f520,f547])).
% 0.21/0.55  fof(f547,plain,(
% 0.21/0.55    k1_xboole_0 = sK5),
% 0.21/0.55    inference(subsumption_resolution,[],[f546,f108])).
% 0.21/0.55  fof(f546,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,sK5) | k1_xboole_0 = sK5),
% 0.21/0.55    inference(forward_demodulation,[],[f545,f110])).
% 0.21/0.55  fof(f545,plain,(
% 0.21/0.55    ~r1_tarski(k2_zfmisc_1(sK2,k1_xboole_0),sK5) | k1_xboole_0 = sK5),
% 0.21/0.55    inference(forward_demodulation,[],[f544,f413])).
% 0.21/0.55  fof(f544,plain,(
% 0.21/0.55    k1_xboole_0 = sK5 | ~r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK5)),
% 0.21/0.55    inference(forward_demodulation,[],[f437,f110])).
% 0.21/0.55  fof(f437,plain,(
% 0.21/0.55    sK5 = k2_zfmisc_1(sK2,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK5)),
% 0.21/0.55    inference(backward_demodulation,[],[f165,f413])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    ~r1_tarski(k2_zfmisc_1(sK2,k1_tarski(sK3)),sK5) | k2_zfmisc_1(sK2,k1_tarski(sK3)) = sK5),
% 0.21/0.55    inference(resolution,[],[f152,f74])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    r1_tarski(sK5,k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.21/0.55    inference(resolution,[],[f65,f103])).
% 0.21/0.55  fof(f520,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k5_partfun1(sK2,k1_xboole_0,sK5)) | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f519,f413])).
% 0.21/0.55  fof(f519,plain,(
% 0.21/0.55    ( ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK5))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f433,f110])).
% 0.21/0.55  fof(f433,plain,(
% 0.21/0.55    ( ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | ~r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK5))) )),
% 0.21/0.55    inference(backward_demodulation,[],[f159,f413])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK5)) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f147,f63])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k5_partfun1(sK2,k1_tarski(sK3),sK5)) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | ~v1_funct_1(sK5)) )),
% 0.21/0.55    inference(resolution,[],[f65,f96])).
% 0.21/0.55  fof(f1019,plain,(
% 0.21/0.55    ( ! [X2,X1] : (X1 = X2 | ~r1_tarski(X1,X2)) )),
% 0.21/0.55    inference(resolution,[],[f1014,f74])).
% 0.21/0.55  fof(f1031,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) != X0) )),
% 0.21/0.55    inference(superposition,[],[f551,f1021])).
% 0.21/0.55  fof(f551,plain,(
% 0.21/0.55    k1_xboole_0 != k1_tarski(k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f384,f547])).
% 0.21/0.55  fof(f384,plain,(
% 0.21/0.55    k1_xboole_0 != k1_tarski(sK5)),
% 0.21/0.55    inference(backward_demodulation,[],[f66,f383])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (26437)------------------------------
% 0.21/0.55  % (26437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26437)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (26437)Memory used [KB]: 2174
% 0.21/0.55  % (26437)Time elapsed: 0.088 s
% 0.21/0.55  % (26437)------------------------------
% 0.21/0.55  % (26437)------------------------------
% 0.21/0.55  % (26425)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (26453)Refutation not found, incomplete strategy% (26453)------------------------------
% 0.21/0.55  % (26453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26453)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26453)Memory used [KB]: 1663
% 0.21/0.55  % (26453)Time elapsed: 0.148 s
% 0.21/0.55  % (26453)------------------------------
% 0.21/0.55  % (26453)------------------------------
% 0.21/0.56  % (26422)Success in time 0.198 s
%------------------------------------------------------------------------------
