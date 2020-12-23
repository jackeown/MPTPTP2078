%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0369+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:37 EST 2020

% Result     : Theorem 55.81s
% Output     : CNFRefutation 55.81s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 296 expanded)
%              Number of clauses        :   70 (  87 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  290 ( 791 expanded)
%              Number of equality atoms :  147 ( 271 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f511,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f512,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f511])).

fof(f820,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f512])).

fof(f821,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f820])).

fof(f1065,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK75,k3_subset_1(X0,X1))
        & ~ r2_hidden(sK75,X1)
        & m1_subset_1(sK75,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1064,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ? [X2] :
            ( ~ r2_hidden(X2,k3_subset_1(X0,sK74))
            & ~ r2_hidden(X2,sK74)
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK74,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1063,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(X0)) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(sK73,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,sK73) )
          & m1_subset_1(X1,k1_zfmisc_1(sK73)) )
      & k1_xboole_0 != sK73 ) ),
    introduced(choice_axiom,[])).

fof(f1066,plain,
    ( ~ r2_hidden(sK75,k3_subset_1(sK73,sK74))
    & ~ r2_hidden(sK75,sK74)
    & m1_subset_1(sK75,sK73)
    & m1_subset_1(sK74,k1_zfmisc_1(sK73))
    & k1_xboole_0 != sK73 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK73,sK74,sK75])],[f821,f1065,f1064,f1063])).

fof(f1819,plain,(
    m1_subset_1(sK75,sK73) ),
    inference(cnf_transformation,[],[f1066])).

fof(f455,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f760,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f455])).

fof(f1029,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f760])).

fof(f1736,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1029])).

fof(f1817,plain,(
    k1_xboole_0 != sK73 ),
    inference(cnf_transformation,[],[f1066])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1080,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2259,plain,(
    o_0_0_xboole_0 != sK73 ),
    inference(definition_unfolding,[],[f1817,f1080])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f607,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f1255,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f607])).

fof(f1952,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f1255,f1080])).

fof(f424,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1010,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f424])).

fof(f1688,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1010])).

fof(f2213,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1688,f1080])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1076,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1228,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1844,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f1076,f1228,f1228])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1218,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1925,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f1218,f1080])).

fof(f109,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1227,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

fof(f1934,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1227,f1228])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1155,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1841,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f1155,f1228])).

fof(f464,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1748,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f464])).

fof(f481,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1766,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f481])).

fof(f421,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1008,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f421])).

fof(f1683,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1008])).

fof(f1820,plain,(
    ~ r2_hidden(sK75,sK74) ),
    inference(cnf_transformation,[],[f1066])).

fof(f98,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f582,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f98])).

fof(f1216,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f582])).

fof(f1923,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(definition_unfolding,[],[f1216,f1080])).

fof(f1821,plain,(
    ~ r2_hidden(sK75,k3_subset_1(sK73,sK74)) ),
    inference(cnf_transformation,[],[f1066])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1292,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1288,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f1828,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1288,f1228])).

fof(f1974,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1292,f1828])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1285,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1077,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1226,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f1933,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f1226,f1080,f1828])).

fof(f51,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1158,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1879,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f1158,f1228])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1286,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f1971,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f1286,f1080])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1242,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1944,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f1242,f1080])).

fof(f505,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f811,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f505])).

fof(f1058,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f811])).

fof(f1808,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1058])).

fof(f423,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1009,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f423])).

fof(f1685,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f1009])).

fof(f1818,plain,(
    m1_subset_1(sK74,k1_zfmisc_1(sK73)) ),
    inference(cnf_transformation,[],[f1066])).

cnf(c_732,negated_conjecture,
    ( m1_subset_1(sK75,sK73) ),
    inference(cnf_transformation,[],[f1819])).

cnf(c_17734,plain,
    ( m1_subset_1(sK75,sK73) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1736])).

cnf(c_17806,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_175628,plain,
    ( r2_hidden(sK75,sK73) = iProver_top
    | v1_xboole_0(sK73) = iProver_top ),
    inference(superposition,[status(thm)],[c_17734,c_17806])).

cnf(c_734,negated_conjecture,
    ( o_0_0_xboole_0 != sK73 ),
    inference(cnf_transformation,[],[f2259])).

cnf(c_742,plain,
    ( m1_subset_1(sK75,sK73) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_181,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1952])).

cnf(c_22545,plain,
    ( ~ v1_xboole_0(sK73)
    | o_0_0_xboole_0 = sK73 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_22546,plain,
    ( o_0_0_xboole_0 = sK73
    | v1_xboole_0(sK73) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22545])).

cnf(c_26987,plain,
    ( ~ m1_subset_1(X0,sK73)
    | r2_hidden(X0,sK73)
    | v1_xboole_0(sK73) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_42839,plain,
    ( ~ m1_subset_1(sK75,sK73)
    | r2_hidden(sK75,sK73)
    | v1_xboole_0(sK73) ),
    inference(instantiation,[status(thm)],[c_26987])).

cnf(c_42840,plain,
    ( m1_subset_1(sK75,sK73) != iProver_top
    | r2_hidden(sK75,sK73) = iProver_top
    | v1_xboole_0(sK73) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42839])).

cnf(c_177477,plain,
    ( r2_hidden(sK75,sK73) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_175628,c_734,c_742,c_22546,c_42840])).

cnf(c_602,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2213])).

cnf(c_17951,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = o_0_0_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_194258,plain,
    ( k4_xboole_0(k1_tarski(sK75),sK73) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_177477,c_17951])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1844])).

cnf(c_195165,plain,
    ( k4_xboole_0(sK73,k4_xboole_0(sK73,k1_tarski(sK75))) = k4_xboole_0(k1_tarski(sK75),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_194258,c_6])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1925])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1934])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1841])).

cnf(c_24060,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_154,c_1])).

cnf(c_195179,plain,
    ( k4_xboole_0(sK73,k4_xboole_0(sK73,k1_tarski(sK75))) = k1_tarski(sK75) ),
    inference(demodulation,[status(thm)],[c_195165,c_145,c_24060])).

cnf(c_662,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1748])).

cnf(c_17799,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_680,plain,
    ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1766])).

cnf(c_18290,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17799,c_680])).

cnf(c_201870,plain,
    ( m1_subset_1(k1_tarski(sK75),k1_zfmisc_1(sK73)) = iProver_top ),
    inference(superposition,[status(thm)],[c_195179,c_18290])).

cnf(c_597,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f1683])).

cnf(c_17838,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_731,negated_conjecture,
    ( ~ r2_hidden(sK75,sK74) ),
    inference(cnf_transformation,[],[f1820])).

cnf(c_17735,plain,
    ( r2_hidden(sK75,sK74) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_112191,plain,
    ( k4_xboole_0(sK74,k1_tarski(sK75)) = sK74 ),
    inference(superposition,[status(thm)],[c_17838,c_17735])).

cnf(c_143,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1923])).

cnf(c_18095,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_130588,plain,
    ( k1_tarski(sK75) = o_0_0_xboole_0
    | r1_tarski(k1_tarski(sK75),sK74) != iProver_top ),
    inference(superposition,[status(thm)],[c_112191,c_18095])).

cnf(c_730,negated_conjecture,
    ( ~ r2_hidden(sK75,k3_subset_1(sK73,sK74)) ),
    inference(cnf_transformation,[],[f1821])).

cnf(c_17736,plain,
    ( r2_hidden(sK75,k3_subset_1(sK73,sK74)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_112190,plain,
    ( k4_xboole_0(k3_subset_1(sK73,sK74),k1_tarski(sK75)) = k3_subset_1(sK73,sK74) ),
    inference(superposition,[status(thm)],[c_17838,c_17736])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1974])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1285])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1077])).

cnf(c_8850,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_153,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1933])).

cnf(c_8871,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_153,c_211,c_7])).

cnf(c_18767,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8850,c_8871])).

cnf(c_85,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1879])).

cnf(c_18136,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_41801,plain,
    ( r1_xboole_0(k4_xboole_0(X0,o_0_0_xboole_0),k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18767,c_18136])).

cnf(c_41845,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41801,c_145])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1971])).

cnf(c_24076,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1944])).

cnf(c_23099,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_24095,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_24076,c_23099])).

cnf(c_41846,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_41845,c_24095])).

cnf(c_113778,plain,
    ( r1_xboole_0(k1_tarski(sK75),k3_subset_1(sK73,sK74)) = iProver_top ),
    inference(superposition,[status(thm)],[c_112190,c_41846])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_subset_1(X1,X0))
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f1808])).

cnf(c_17743,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X2,k3_subset_1(X1,X0)) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_116991,plain,
    ( m1_subset_1(k1_tarski(sK75),k1_zfmisc_1(sK73)) != iProver_top
    | m1_subset_1(sK74,k1_zfmisc_1(sK73)) != iProver_top
    | r1_tarski(k1_tarski(sK75),sK74) = iProver_top ),
    inference(superposition,[status(thm)],[c_113778,c_17743])).

cnf(c_8918,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_99224,plain,
    ( k4_xboole_0(k1_tarski(sK75),sK73) != X0
    | k4_xboole_0(k1_tarski(sK75),sK73) = k1_tarski(sK75)
    | k1_tarski(sK75) != X0 ),
    inference(instantiation,[status(thm)],[c_8918])).

cnf(c_99235,plain,
    ( k4_xboole_0(k1_tarski(sK75),sK73) = k1_tarski(sK75)
    | k4_xboole_0(k1_tarski(sK75),sK73) != o_0_0_xboole_0
    | k1_tarski(sK75) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_99224])).

cnf(c_601,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1685])).

cnf(c_53613,plain,
    ( ~ r2_hidden(sK75,sK73)
    | k4_xboole_0(k1_tarski(sK75),sK73) != k1_tarski(sK75) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_53617,plain,
    ( ~ r2_hidden(sK75,sK73)
    | k4_xboole_0(k1_tarski(sK75),sK73) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_733,negated_conjecture,
    ( m1_subset_1(sK74,k1_zfmisc_1(sK73)) ),
    inference(cnf_transformation,[],[f1818])).

cnf(c_741,plain,
    ( m1_subset_1(sK74,k1_zfmisc_1(sK73)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_201870,c_130588,c_116991,c_99235,c_53613,c_53617,c_42839,c_22545,c_732,c_741,c_734])).

%------------------------------------------------------------------------------
