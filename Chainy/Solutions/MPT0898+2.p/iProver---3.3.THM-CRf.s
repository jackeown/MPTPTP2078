%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0898+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:56 EST 2020

% Result     : Theorem 38.81s
% Output     : CNFRefutation 38.81s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 211 expanded)
%              Number of clauses        :   19 (  35 expanded)
%              Number of leaves         :    9 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 411 expanded)
%              Number of equality atoms :  126 ( 410 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1355,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1356,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1355])).

fof(f2730,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f1356])).

fof(f3763,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK393 != sK394
      & k4_zfmisc_1(sK393,sK393,sK393,sK393) = k4_zfmisc_1(sK394,sK394,sK394,sK394) ) ),
    introduced(choice_axiom,[])).

fof(f3764,plain,
    ( sK393 != sK394
    & k4_zfmisc_1(sK393,sK393,sK393,sK393) = k4_zfmisc_1(sK394,sK394,sK394,sK394) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK393,sK394])],[f2730,f3763])).

fof(f6152,plain,(
    k4_zfmisc_1(sK393,sK393,sK393,sK393) = k4_zfmisc_1(sK394,sK394,sK394,sK394) ),
    inference(cnf_transformation,[],[f3764])).

fof(f1277,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5970,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5968,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f6175,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f5970,f5968])).

fof(f6964,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK393),sK393),sK393) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK394,sK394),sK394),sK394) ),
    inference(definition_unfolding,[],[f6152,f6175,f6175])).

fof(f1332,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2713,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1332])).

fof(f2714,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f2713])).

fof(f6106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2714])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3778,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6918,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f6106,f3778,f5968,f5968,f5968])).

fof(f6153,plain,(
    sK393 != sK394 ),
    inference(cnf_transformation,[],[f3764])).

fof(f6107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2714])).

fof(f6917,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f6107,f3778,f5968,f5968,f5968])).

fof(f1352,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3761,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1352])).

fof(f3762,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f3761])).

fof(f6139,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3762])).

fof(f6955,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6139,f3778,f6175,f3778,f3778,f3778,f3778])).

cnf(c_2363,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK393),sK393),sK393) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK394,sK394),sK394),sK394) ),
    inference(cnf_transformation,[],[f6964])).

cnf(c_2316,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6918])).

cnf(c_111282,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK394,sK394),sK394),sK394) = o_0_0_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK393),sK393),sK393) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK394 = X1 ),
    inference(superposition,[status(thm)],[c_2363,c_2316])).

cnf(c_111399,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK393),sK393),sK393) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK393),sK393),sK393) = o_0_0_xboole_0
    | sK394 = X1 ),
    inference(demodulation,[status(thm)],[c_111282,c_2363])).

cnf(c_2362,negated_conjecture,
    ( sK393 != sK394 ),
    inference(cnf_transformation,[],[f6153])).

cnf(c_2315,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6917])).

cnf(c_110995,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = o_0_0_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK393),sK393),sK393) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK394 = X2 ),
    inference(superposition,[status(thm)],[c_2363,c_2315])).

cnf(c_114825,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK393),sK393),sK393) = o_0_0_xboole_0
    | sK394 = sK393 ),
    inference(equality_resolution,[status(thm)],[c_110995])).

cnf(c_33229,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_88229,plain,
    ( sK394 != X0
    | sK393 != X0
    | sK393 = sK394 ),
    inference(instantiation,[status(thm)],[c_33229])).

cnf(c_117571,plain,
    ( sK394 != sK393
    | sK393 = sK394
    | sK393 != sK393 ),
    inference(instantiation,[status(thm)],[c_88229])).

cnf(c_33228,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_117572,plain,
    ( sK393 = sK393 ),
    inference(instantiation,[status(thm)],[c_33228])).

cnf(c_118469,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK393),sK393),sK393) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_111399,c_2362,c_114825,c_117571,c_117572])).

cnf(c_2353,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f6955])).

cnf(c_118699,plain,
    ( sK393 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_118469,c_2353])).

cnf(c_113823,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK393),sK393),sK393) != o_0_0_xboole_0
    | sK394 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2363,c_2353])).

cnf(c_88230,plain,
    ( sK394 != o_0_0_xboole_0
    | sK393 = sK394
    | sK393 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_88229])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_118699,c_117572,c_117571,c_114825,c_113823,c_88230,c_2362])).

%------------------------------------------------------------------------------
