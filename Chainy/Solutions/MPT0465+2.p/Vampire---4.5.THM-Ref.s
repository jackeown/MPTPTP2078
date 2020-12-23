%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0465+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 118 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   21
%              Number of atoms          :  181 ( 427 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4337,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4336,f1323])).

fof(f1323,plain,(
    v1_relat_1(sK43) ),
    inference(cnf_transformation,[],[f1054])).

fof(f1054,plain,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK42,sK43),k5_relat_1(sK42,sK44)),k5_relat_1(sK42,k6_subset_1(sK43,sK44)))
    & v1_relat_1(sK44)
    & v1_relat_1(sK43)
    & v1_relat_1(sK42) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK42,sK43,sK44])],[f699,f1053,f1052,f1051])).

fof(f1051,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK42,X1),k5_relat_1(sK42,X2)),k5_relat_1(sK42,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK42) ) ),
    introduced(choice_axiom,[])).

fof(f1052,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK42,X1),k5_relat_1(sK42,X2)),k5_relat_1(sK42,k6_subset_1(X1,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK42,sK43),k5_relat_1(sK42,X2)),k5_relat_1(sK42,k6_subset_1(sK43,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK43) ) ),
    introduced(choice_axiom,[])).

fof(f1053,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK42,sK43),k5_relat_1(sK42,X2)),k5_relat_1(sK42,k6_subset_1(sK43,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK42,sK43),k5_relat_1(sK42,sK44)),k5_relat_1(sK42,k6_subset_1(sK43,sK44)))
      & v1_relat_1(sK44) ) ),
    introduced(choice_axiom,[])).

fof(f699,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f693])).

fof(f693,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f692])).

fof(f692,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relat_1)).

fof(f4336,plain,(
    ~ v1_relat_1(sK43) ),
    inference(subsumption_resolution,[],[f4331,f1324])).

fof(f1324,plain,(
    v1_relat_1(sK44) ),
    inference(cnf_transformation,[],[f1054])).

fof(f4331,plain,
    ( ~ v1_relat_1(sK44)
    | ~ v1_relat_1(sK43) ),
    inference(resolution,[],[f4328,f1395])).

fof(f1395,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f743,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f742])).

fof(f742,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_relat_1)).

fof(f4328,plain,(
    ~ v1_relat_1(k2_xboole_0(sK43,sK44)) ),
    inference(subsumption_resolution,[],[f4322,f1323])).

fof(f4322,plain,
    ( ~ v1_relat_1(k2_xboole_0(sK43,sK44))
    | ~ v1_relat_1(sK43) ),
    inference(resolution,[],[f3962,f1986])).

fof(f1986,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f1397,f1369])).

fof(f1369,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f1397,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f745])).

fof(f745,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f653])).

fof(f653,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f3962,plain,
    ( ~ v1_relat_1(k6_subset_1(sK43,sK44))
    | ~ v1_relat_1(k2_xboole_0(sK43,sK44)) ),
    inference(subsumption_resolution,[],[f3961,f1322])).

fof(f1322,plain,(
    v1_relat_1(sK42) ),
    inference(cnf_transformation,[],[f1054])).

fof(f3961,plain,
    ( ~ v1_relat_1(k6_subset_1(sK43,sK44))
    | ~ v1_relat_1(k2_xboole_0(sK43,sK44))
    | ~ v1_relat_1(sK42) ),
    inference(subsumption_resolution,[],[f3960,f1323])).

fof(f3960,plain,
    ( ~ v1_relat_1(k6_subset_1(sK43,sK44))
    | ~ v1_relat_1(k2_xboole_0(sK43,sK44))
    | ~ v1_relat_1(sK43)
    | ~ v1_relat_1(sK42) ),
    inference(subsumption_resolution,[],[f3959,f2219])).

fof(f2219,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1351])).

fof(f1351,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1072])).

fof(f1072,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1071])).

fof(f1071,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3959,plain,
    ( ~ v1_relat_1(k6_subset_1(sK43,sK44))
    | ~ r1_tarski(sK42,sK42)
    | ~ v1_relat_1(k2_xboole_0(sK43,sK44))
    | ~ v1_relat_1(sK43)
    | ~ v1_relat_1(sK42) ),
    inference(subsumption_resolution,[],[f3958,f1367])).

fof(f1367,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3958,plain,
    ( ~ v1_relat_1(k6_subset_1(sK43,sK44))
    | ~ r1_tarski(sK43,k2_xboole_0(sK43,sK44))
    | ~ r1_tarski(sK42,sK42)
    | ~ v1_relat_1(k2_xboole_0(sK43,sK44))
    | ~ v1_relat_1(sK43)
    | ~ v1_relat_1(sK42) ),
    inference(duplicate_literal_removal,[],[f3950])).

fof(f3950,plain,
    ( ~ v1_relat_1(k6_subset_1(sK43,sK44))
    | ~ r1_tarski(sK43,k2_xboole_0(sK43,sK44))
    | ~ r1_tarski(sK42,sK42)
    | ~ v1_relat_1(k2_xboole_0(sK43,sK44))
    | ~ v1_relat_1(sK43)
    | ~ v1_relat_1(sK42)
    | ~ v1_relat_1(sK42) ),
    inference(resolution,[],[f2497,f1375])).

fof(f1375,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f728])).

fof(f728,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f727])).

fof(f727,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f689])).

fof(f689,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(f2497,plain,
    ( ~ r1_tarski(k5_relat_1(sK42,sK43),k5_relat_1(sK42,k2_xboole_0(sK43,sK44)))
    | ~ v1_relat_1(k6_subset_1(sK43,sK44)) ),
    inference(forward_demodulation,[],[f2496,f1431])).

fof(f1431,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2496,plain,
    ( ~ r1_tarski(k5_relat_1(sK42,sK43),k5_relat_1(sK42,k2_xboole_0(sK44,sK43)))
    | ~ v1_relat_1(k6_subset_1(sK43,sK44)) ),
    inference(forward_demodulation,[],[f2495,f2076])).

fof(f2076,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f1587,f1369])).

fof(f1587,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2495,plain,
    ( ~ r1_tarski(k5_relat_1(sK42,sK43),k5_relat_1(sK42,k2_xboole_0(sK44,k6_subset_1(sK43,sK44))))
    | ~ v1_relat_1(k6_subset_1(sK43,sK44)) ),
    inference(subsumption_resolution,[],[f2494,f1322])).

fof(f2494,plain,
    ( ~ r1_tarski(k5_relat_1(sK42,sK43),k5_relat_1(sK42,k2_xboole_0(sK44,k6_subset_1(sK43,sK44))))
    | ~ v1_relat_1(k6_subset_1(sK43,sK44))
    | ~ v1_relat_1(sK42) ),
    inference(subsumption_resolution,[],[f2490,f1324])).

fof(f2490,plain,
    ( ~ r1_tarski(k5_relat_1(sK42,sK43),k5_relat_1(sK42,k2_xboole_0(sK44,k6_subset_1(sK43,sK44))))
    | ~ v1_relat_1(k6_subset_1(sK43,sK44))
    | ~ v1_relat_1(sK44)
    | ~ v1_relat_1(sK42) ),
    inference(superposition,[],[f2287,f1389])).

fof(f1389,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f735])).

fof(f735,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f690])).

fof(f690,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relat_1)).

fof(f2287,plain,(
    ~ r1_tarski(k5_relat_1(sK42,sK43),k2_xboole_0(k5_relat_1(sK42,sK44),k5_relat_1(sK42,k6_subset_1(sK43,sK44)))) ),
    inference(resolution,[],[f1325,f2043])).

fof(f2043,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f1554,f1369])).

fof(f1554,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f803])).

fof(f803,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1325,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1(sK42,sK43),k5_relat_1(sK42,sK44)),k5_relat_1(sK42,k6_subset_1(sK43,sK44))) ),
    inference(cnf_transformation,[],[f1054])).
%------------------------------------------------------------------------------
