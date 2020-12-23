%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0414+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:39 EST 2020

% Result     : Theorem 19.57s
% Output     : CNFRefutation 19.57s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 232 expanded)
%              Number of clauses        :   47 (  93 expanded)
%              Number of leaves         :    8 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  306 (1143 expanded)
%              Number of equality atoms :  113 ( 240 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1328,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f586])).

fof(f2268,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1328])).

fof(f589,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f590,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f589])).

fof(f973,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f590])).

fof(f974,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f973])).

fof(f1329,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f974])).

fof(f1331,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( sK117 != X1
        & ! [X3] :
            ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,sK117) )
              & ( r2_hidden(X3,sK117)
                | ~ r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK117,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1330,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK116 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK116)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK116) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK115)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK115))) )
      & m1_subset_1(sK116,k1_zfmisc_1(k1_zfmisc_1(sK115))) ) ),
    introduced(choice_axiom,[])).

fof(f1332,plain,
    ( sK116 != sK117
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK116)
            | ~ r2_hidden(X3,sK117) )
          & ( r2_hidden(X3,sK117)
            | ~ r2_hidden(X3,sK116) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK115)) )
    & m1_subset_1(sK117,k1_zfmisc_1(k1_zfmisc_1(sK115)))
    & m1_subset_1(sK116,k1_zfmisc_1(k1_zfmisc_1(sK115))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK115,sK116,sK117])],[f1329,f1331,f1330])).

fof(f2272,plain,(
    m1_subset_1(sK116,k1_zfmisc_1(k1_zfmisc_1(sK115))) ),
    inference(cnf_transformation,[],[f1332])).

fof(f2273,plain,(
    m1_subset_1(sK117,k1_zfmisc_1(k1_zfmisc_1(sK115))) ),
    inference(cnf_transformation,[],[f1332])).

fof(f539,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f943,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f539])).

fof(f944,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f943])).

fof(f1285,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f944])).

fof(f1286,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f1285])).

fof(f1287,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK90(X0,X1,X2),X2)
          | ~ r2_hidden(sK90(X0,X1,X2),X1) )
        & ( r2_hidden(sK90(X0,X1,X2),X2)
          | r2_hidden(sK90(X0,X1,X2),X1) )
        & m1_subset_1(sK90(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1288,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK90(X0,X1,X2),X2)
              | ~ r2_hidden(sK90(X0,X1,X2),X1) )
            & ( r2_hidden(sK90(X0,X1,X2),X2)
              | r2_hidden(sK90(X0,X1,X2),X1) )
            & m1_subset_1(sK90(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK90])],[f1286,f1287])).

fof(f2188,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | r2_hidden(sK90(X0,X1,X2),X2)
      | r2_hidden(sK90(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1288])).

fof(f2269,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1328])).

fof(f2187,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK90(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1288])).

fof(f2275,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK116)
      | ~ r2_hidden(X3,sK117)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK115)) ) ),
    inference(cnf_transformation,[],[f1332])).

fof(f2276,plain,(
    sK116 != sK117 ),
    inference(cnf_transformation,[],[f1332])).

fof(f2189,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK90(X0,X1,X2),X2)
      | ~ r2_hidden(sK90(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1288])).

fof(f2274,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK117)
      | ~ r2_hidden(X3,sK116)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK115)) ) ),
    inference(cnf_transformation,[],[f1332])).

cnf(c_920,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2268])).

cnf(c_927,negated_conjecture,
    ( m1_subset_1(sK116,k1_zfmisc_1(k1_zfmisc_1(sK115))) ),
    inference(cnf_transformation,[],[f2272])).

cnf(c_52420,plain,
    ( r1_tarski(sK116,k1_zfmisc_1(sK115)) ),
    inference(resolution,[status(thm)],[c_920,c_927])).

cnf(c_926,negated_conjecture,
    ( m1_subset_1(sK117,k1_zfmisc_1(k1_zfmisc_1(sK115))) ),
    inference(cnf_transformation,[],[f2273])).

cnf(c_52418,plain,
    ( r1_tarski(sK117,k1_zfmisc_1(sK115)) ),
    inference(resolution,[status(thm)],[c_920,c_926])).

cnf(c_839,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK90(X1,X2,X0),X0)
    | r2_hidden(sK90(X1,X2,X0),X2)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f2188])).

cnf(c_919,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2269])).

cnf(c_5000,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_919])).

cnf(c_5001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_5000])).

cnf(c_6218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | r2_hidden(sK90(X1,X0,X2),X2)
    | r2_hidden(sK90(X1,X0,X2),X0)
    | X2 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_839,c_5001])).

cnf(c_9222,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_919])).

cnf(c_9223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_9222])).

cnf(c_10409,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r2_hidden(sK90(X1,X0,X2),X2)
    | r2_hidden(sK90(X1,X0,X2),X0)
    | X2 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_6218,c_9223])).

cnf(c_24123,plain,
    ( X0 = X1
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r2_hidden(sK90(X2,X1,X0),X0) = iProver_top
    | r2_hidden(sK90(X2,X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10409])).

cnf(c_840,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK90(X1,X2,X0),X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f2187])).

cnf(c_6219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK90(X1,X0,X2),X1)
    | ~ r1_tarski(X2,X1)
    | X2 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_840,c_5001])).

cnf(c_10410,plain,
    ( m1_subset_1(sK90(X0,X1,X2),X0)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0)
    | X2 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_6219,c_9223])).

cnf(c_24122,plain,
    ( X0 = X1
    | m1_subset_1(sK90(X2,X1,X0),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10410])).

cnf(c_924,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK115))
    | ~ r2_hidden(X0,sK117)
    | r2_hidden(X0,sK116) ),
    inference(cnf_transformation,[],[f2275])).

cnf(c_24221,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(X0,sK117) != iProver_top
    | r2_hidden(X0,sK116) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_35426,plain,
    ( X0 = X1
    | r1_tarski(X1,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),X0,X1),sK117) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),X0,X1),sK116) = iProver_top ),
    inference(superposition,[status(thm)],[c_24122,c_24221])).

cnf(c_39918,plain,
    ( sK117 = X0
    | r1_tarski(X0,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),sK117,X0),X0) = iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),sK117,X0),sK116) = iProver_top ),
    inference(superposition,[status(thm)],[c_24123,c_35426])).

cnf(c_40559,plain,
    ( sK117 = sK116
    | r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),sK117,sK116),sK116) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_39918])).

cnf(c_40561,plain,
    ( sK117 = sK116
    | r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),sK117,sK116),sK116) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_40559])).

cnf(c_923,negated_conjecture,
    ( sK116 != sK117 ),
    inference(cnf_transformation,[],[f2276])).

cnf(c_12076,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_32896,plain,
    ( sK117 != X0
    | sK116 != X0
    | sK116 = sK117 ),
    inference(instantiation,[status(thm)],[c_12076])).

cnf(c_38708,plain,
    ( sK117 != sK116
    | sK116 = sK117
    | sK116 != sK116 ),
    inference(instantiation,[status(thm)],[c_32896])).

cnf(c_12075,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_38709,plain,
    ( sK116 = sK116 ),
    inference(instantiation,[status(thm)],[c_12075])).

cnf(c_41658,plain,
    ( r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),sK117,sK116),sK116) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40561,c_923,c_38708,c_38709])).

cnf(c_838,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK90(X1,X2,X0),X0)
    | ~ r2_hidden(sK90(X1,X2,X0),X2)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f2189])).

cnf(c_6217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(sK90(X1,X0,X2),X2)
    | ~ r2_hidden(sK90(X1,X0,X2),X0)
    | X2 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_838,c_5001])).

cnf(c_10408,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(sK90(X1,X0,X2),X2)
    | ~ r2_hidden(sK90(X1,X0,X2),X0)
    | X2 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_6217,c_9223])).

cnf(c_24124,plain,
    ( X0 = X1
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r2_hidden(sK90(X2,X1,X0),X0) != iProver_top
    | r2_hidden(sK90(X2,X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10408])).

cnf(c_46336,plain,
    ( sK117 = sK116
    | r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),sK117,sK116),sK117) != iProver_top ),
    inference(superposition,[status(thm)],[c_41658,c_24124])).

cnf(c_925,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK115))
    | r2_hidden(X0,sK117)
    | ~ r2_hidden(X0,sK116) ),
    inference(cnf_transformation,[],[f2274])).

cnf(c_24220,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(X0,sK117) = iProver_top
    | r2_hidden(X0,sK116) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_35427,plain,
    ( X0 = X1
    | r1_tarski(X1,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),X0,X1),sK117) = iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),X0,X1),sK116) != iProver_top ),
    inference(superposition,[status(thm)],[c_24122,c_24220])).

cnf(c_39921,plain,
    ( sK116 = X0
    | r1_tarski(X0,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),X0,sK116),X0) = iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),X0,sK116),sK117) = iProver_top ),
    inference(superposition,[status(thm)],[c_24123,c_35427])).

cnf(c_41523,plain,
    ( sK117 = sK116
    | r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),sK117,sK116),sK117) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_39921])).

cnf(c_41525,plain,
    ( sK117 = sK116
    | r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),sK117,sK116),sK117) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_41523])).

cnf(c_44791,plain,
    ( r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top
    | r2_hidden(sK90(k1_zfmisc_1(sK115),sK117,sK116),sK117) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41525,c_923,c_38708,c_38709])).

cnf(c_50204,plain,
    ( r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46336,c_923,c_38708,c_38709,c_44791])).

cnf(c_50205,plain,
    ( r1_tarski(sK117,k1_zfmisc_1(sK115)) != iProver_top
    | r1_tarski(sK116,k1_zfmisc_1(sK115)) != iProver_top ),
    inference(renaming,[status(thm)],[c_50204])).

cnf(c_50206,plain,
    ( ~ r1_tarski(sK117,k1_zfmisc_1(sK115))
    | ~ r1_tarski(sK116,k1_zfmisc_1(sK115)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_50205])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52420,c_52418,c_50206])).

%------------------------------------------------------------------------------
