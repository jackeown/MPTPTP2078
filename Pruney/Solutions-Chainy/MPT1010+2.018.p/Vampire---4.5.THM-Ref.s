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
% DateTime   : Thu Dec  3 13:04:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 206 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  369 ( 857 expanded)
%              Number of equality atoms :  180 ( 374 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(subsumption_resolution,[],[f175,f47])).

fof(f47,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f175,plain,(
    sK1 = k1_funct_1(sK3,sK2) ),
    inference(resolution,[],[f173,f46])).

fof(f46,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f173,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = k1_funct_1(sK3,X2) ) ),
    inference(forward_demodulation,[],[f172,f151])).

fof(f151,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f143,f109])).

fof(f109,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f107,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f105,f75])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f143,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | sK0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f83,f133])).

fof(f133,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f132,f126])).

fof(f126,plain,(
    k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f69,f80])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f45,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f76,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f132,plain,
    ( sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f131,f81])).

fof(f81,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f44,f79])).

% (28896)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f44,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f131,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) ),
    inference(resolution,[],[f63,f80])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f83,plain,(
    ! [X6,X2,X0,X1] : r2_hidden(X6,k2_enumset1(X0,X1,X2,X6)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X6) != X4 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK4(X0,X1,X2,X3,X4) != X3
              & sK4(X0,X1,X2,X3,X4) != X2
              & sK4(X0,X1,X2,X3,X4) != X1
              & sK4(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4),X4) )
          & ( sK4(X0,X1,X2,X3,X4) = X3
            | sK4(X0,X1,X2,X3,X4) = X2
            | sK4(X0,X1,X2,X3,X4) = X1
            | sK4(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK4(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK4(X0,X1,X2,X3,X4) != X3
            & sK4(X0,X1,X2,X3,X4) != X2
            & sK4(X0,X1,X2,X3,X4) != X1
            & sK4(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4),X4) )
        & ( sK4(X0,X1,X2,X3,X4) = X3
          | sK4(X0,X1,X2,X3,X4) = X2
          | sK4(X0,X1,X2,X3,X4) = X1
          | sK4(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK4(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(f172,plain,(
    ! [X2] :
      ( sK1 = k1_funct_1(sK3,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f171,f114])).

fof(f114,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f80,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f171,plain,(
    ! [X2] :
      ( sK1 = k1_funct_1(sK3,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f169,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f169,plain,(
    ! [X2] :
      ( sK1 = k1_funct_1(sK3,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK3))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f167,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f167,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,(
    ! [X0] :
      ( sK1 = X0
      | sK1 = X0
      | sK1 = X0
      | ~ r2_hidden(X0,k2_relat_1(sK3))
      | sK1 = X0 ) ),
    inference(resolution,[],[f157,f117])).

fof(f117,plain,(
    r1_tarski(k2_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f116,f113])).

fof(f113,plain,(
    v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f80,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f116,plain,(
    ! [X1] :
      ( ~ v5_relat_1(sK3,X1)
      | r1_tarski(k2_relat_1(sK3),X1) ) ),
    inference(resolution,[],[f114,f72])).

% (28895)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f157,plain,(
    ! [X21,X19,X17,X20,X18,X16] :
      ( ~ r1_tarski(X21,k2_enumset1(X19,X18,X16,X20))
      | X17 = X18
      | X17 = X19
      | X17 = X20
      | ~ r2_hidden(X17,X21)
      | X16 = X17 ) ),
    inference(resolution,[],[f90,f60])).

fof(f90,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(X6,k2_enumset1(X0,X1,X2,X3))
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | X3 = X6 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X3 = X6
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | ~ r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:07:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (28899)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (28912)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (28899)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (28907)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f175,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    sK1 != k1_funct_1(sK3,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.52    inference(negated_conjecture,[],[f14])).
% 0.22/0.52  fof(f14,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    sK1 = k1_funct_1(sK3,sK2)),
% 0.22/0.52    inference(resolution,[],[f173,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    r2_hidden(sK2,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = k1_funct_1(sK3,X2)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f172,f151])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f143,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f107,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.52    inference(resolution,[],[f105,f75])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | ~r1_tarski(X1,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f60,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    r2_hidden(sK1,k1_xboole_0) | sK0 = k1_relat_1(sK3)),
% 0.22/0.52    inference(superposition,[],[f83,f133])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relat_1(sK3)),
% 0.22/0.52    inference(superposition,[],[f132,f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) = k1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f69,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 0.22/0.52    inference(definition_unfolding,[],[f45,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f71,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f76,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f131,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.52    inference(definition_unfolding,[],[f44,f79])).
% 0.22/0.52  % (28896)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)),
% 0.22/0.52    inference(resolution,[],[f63,f80])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,k2_enumset1(X0,X1,X2,X6))) )),
% 0.22/0.52    inference(equality_resolution,[],[f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | k2_enumset1(X0,X1,X2,X6) != X4) )),
% 0.22/0.52    inference(equality_resolution,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | (((sK4(X0,X1,X2,X3,X4) != X3 & sK4(X0,X1,X2,X3,X4) != X2 & sK4(X0,X1,X2,X3,X4) != X1 & sK4(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4),X4)) & (sK4(X0,X1,X2,X3,X4) = X3 | sK4(X0,X1,X2,X3,X4) = X2 | sK4(X0,X1,X2,X3,X4) = X1 | sK4(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK4(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4))) => (((sK4(X0,X1,X2,X3,X4) != X3 & sK4(X0,X1,X2,X3,X4) != X2 & sK4(X0,X1,X2,X3,X4) != X1 & sK4(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4),X4)) & (sK4(X0,X1,X2,X3,X4) = X3 | sK4(X0,X1,X2,X3,X4) = X2 | sK4(X0,X1,X2,X3,X4) = X1 | sK4(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK4(X0,X1,X2,X3,X4),X4))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(rectify,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(flattening,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(nnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ( ! [X2] : (sK1 = k1_funct_1(sK3,X2) | ~r2_hidden(X2,k1_relat_1(sK3))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f171,f114])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    v1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f80,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    ( ! [X2] : (sK1 = k1_funct_1(sK3,X2) | ~r2_hidden(X2,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f169,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    ( ! [X2] : (sK1 = k1_funct_1(sK3,X2) | ~r2_hidden(X2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f167,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | sK1 = X0) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f161])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 = X0 | sK1 = X0 | sK1 = X0 | ~r2_hidden(X0,k2_relat_1(sK3)) | sK1 = X0) )),
% 0.22/0.52    inference(resolution,[],[f157,f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.52    inference(resolution,[],[f116,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    v5_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.52    inference(resolution,[],[f80,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X1] : (~v5_relat_1(sK3,X1) | r1_tarski(k2_relat_1(sK3),X1)) )),
% 0.22/0.52    inference(resolution,[],[f114,f72])).
% 0.22/0.52  % (28895)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X21,X19,X17,X20,X18,X16] : (~r1_tarski(X21,k2_enumset1(X19,X18,X16,X20)) | X17 = X18 | X17 = X19 | X17 = X20 | ~r2_hidden(X17,X21) | X16 = X17) )),
% 0.22/0.52    inference(resolution,[],[f90,f60])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X6,X2,X0,X3,X1] : (~r2_hidden(X6,k2_enumset1(X0,X1,X2,X3)) | X2 = X6 | X1 = X6 | X0 = X6 | X3 = X6) )),
% 0.22/0.52    inference(equality_resolution,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (28899)------------------------------
% 0.22/0.52  % (28899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28899)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (28899)Memory used [KB]: 6396
% 0.22/0.52  % (28899)Time elapsed: 0.098 s
% 0.22/0.52  % (28899)------------------------------
% 0.22/0.52  % (28899)------------------------------
% 0.22/0.52  % (28894)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (28889)Success in time 0.173 s
%------------------------------------------------------------------------------
