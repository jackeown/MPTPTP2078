%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0419+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:39 EST 2020

% Result     : Theorem 47.43s
% Output     : CNFRefutation 47.43s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 119 expanded)
%              Number of clauses        :   31 (  35 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  229 ( 455 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f631,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1040,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f631])).

fof(f1041,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1040])).

fof(f1042,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1043,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1041,f1042])).

fof(f1383,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1043])).

fof(f595,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1364,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f595])).

fof(f2321,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1364])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1126,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f1127,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1126])).

fof(f1128,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK30(X0,X1),X0)
          | ~ r2_hidden(sK30(X0,X1),X1) )
        & ( r1_tarski(sK30(X0,X1),X0)
          | r2_hidden(sK30(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1129,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK30(X0,X1),X0)
            | ~ r2_hidden(sK30(X0,X1),X1) )
          & ( r1_tarski(sK30(X0,X1),X0)
            | r2_hidden(sK30(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK30])],[f1127,f1128])).

fof(f1744,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1129])).

fof(f2892,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f1744])).

fof(f602,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1003,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f602])).

fof(f1369,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f1003])).

fof(f2332,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1369])).

fof(f2322,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1364])).

fof(f2331,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1369])).

fof(f1384,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1043])).

fof(f1385,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1043])).

fof(f605,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f606,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f605])).

fof(f1007,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f606])).

fof(f1008,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f1007])).

fof(f1371,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(X1,sK119)
        & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,sK119))
        & m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1370,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK118,X2)
          & r1_tarski(k7_setfam_1(sK117,sK118),k7_setfam_1(sK117,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK117))) )
      & m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) ) ),
    introduced(choice_axiom,[])).

fof(f1372,plain,
    ( ~ r1_tarski(sK118,sK119)
    & r1_tarski(k7_setfam_1(sK117,sK118),k7_setfam_1(sK117,sK119))
    & m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117)))
    & m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK117,sK118,sK119])],[f1008,f1371,f1370])).

fof(f2338,plain,(
    ~ r1_tarski(sK118,sK119) ),
    inference(cnf_transformation,[],[f1372])).

fof(f2337,plain,(
    r1_tarski(k7_setfam_1(sK117,sK118),k7_setfam_1(sK117,sK119)) ),
    inference(cnf_transformation,[],[f1372])).

fof(f2336,plain,(
    m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(cnf_transformation,[],[f1372])).

fof(f2335,plain,(
    m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(cnf_transformation,[],[f1372])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f1383])).

cnf(c_159606,plain,
    ( ~ r1_tarski(k7_setfam_1(sK117,sK118),X0)
    | r2_hidden(k3_subset_1(sK117,sK11(sK118,sK119)),X0)
    | ~ r2_hidden(k3_subset_1(sK117,sK11(sK118,sK119)),k7_setfam_1(sK117,sK118)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_230239,plain,
    ( ~ r1_tarski(k7_setfam_1(sK117,sK118),k7_setfam_1(sK117,sK119))
    | r2_hidden(k3_subset_1(sK117,sK11(sK118,sK119)),k7_setfam_1(sK117,sK119))
    | ~ r2_hidden(k3_subset_1(sK117,sK11(sK118,sK119)),k7_setfam_1(sK117,sK118)) ),
    inference(instantiation,[status(thm)],[c_159606])).

cnf(c_54420,plain,
    ( ~ r1_tarski(sK118,X0)
    | r2_hidden(sK11(sK118,sK119),X0)
    | ~ r2_hidden(sK11(sK118,sK119),sK118) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_211059,plain,
    ( ~ r1_tarski(sK118,k1_zfmisc_1(sK117))
    | r2_hidden(sK11(sK118,sK119),k1_zfmisc_1(sK117))
    | ~ r2_hidden(sK11(sK118,sK119),sK118) ),
    inference(instantiation,[status(thm)],[c_54420])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2321])).

cnf(c_70666,plain,
    ( ~ m1_subset_1(sK118,k1_zfmisc_1(X0))
    | r1_tarski(sK118,X0) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_115760,plain,
    ( ~ m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117)))
    | r1_tarski(sK118,k1_zfmisc_1(sK117)) ),
    inference(instantiation,[status(thm)],[c_70666])).

cnf(c_360,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f2892])).

cnf(c_55336,plain,
    ( r1_tarski(X0,sK117)
    | ~ r2_hidden(X0,k1_zfmisc_1(sK117)) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_112817,plain,
    ( r1_tarski(sK11(sK118,sK119),sK117)
    | ~ r2_hidden(sK11(sK118,sK119),k1_zfmisc_1(sK117)) ),
    inference(instantiation,[status(thm)],[c_55336])).

cnf(c_942,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f2332])).

cnf(c_932,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2322])).

cnf(c_5904,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_932])).

cnf(c_5905,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_5904])).

cnf(c_7156,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_942,c_5905])).

cnf(c_54418,plain,
    ( ~ m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ r1_tarski(sK11(sK118,sK119),X0)
    | r2_hidden(k3_subset_1(X0,sK11(sK118,sK119)),k7_setfam_1(X0,sK118))
    | ~ r2_hidden(sK11(sK118,sK119),sK118) ),
    inference(instantiation,[status(thm)],[c_7156])).

cnf(c_82793,plain,
    ( ~ m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117)))
    | ~ r1_tarski(sK11(sK118,sK119),sK117)
    | r2_hidden(k3_subset_1(sK117,sK11(sK118,sK119)),k7_setfam_1(sK117,sK118))
    | ~ r2_hidden(sK11(sK118,sK119),sK118) ),
    inference(instantiation,[status(thm)],[c_54418])).

cnf(c_943,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f2331])).

cnf(c_7157,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_943,c_5905])).

cnf(c_49114,plain,
    ( ~ m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117)))
    | ~ r1_tarski(X0,sK117)
    | r2_hidden(X0,sK119)
    | ~ r2_hidden(k3_subset_1(sK117,X0),k7_setfam_1(sK117,sK119)) ),
    inference(instantiation,[status(thm)],[c_7157])).

cnf(c_71791,plain,
    ( ~ m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117)))
    | ~ r1_tarski(sK11(sK118,sK119),sK117)
    | ~ r2_hidden(k3_subset_1(sK117,sK11(sK118,sK119)),k7_setfam_1(sK117,sK119))
    | r2_hidden(sK11(sK118,sK119),sK119) ),
    inference(instantiation,[status(thm)],[c_49114])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1384])).

cnf(c_47446,plain,
    ( r1_tarski(sK118,sK119)
    | r2_hidden(sK11(sK118,sK119),sK118) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1385])).

cnf(c_47438,plain,
    ( r1_tarski(sK118,sK119)
    | ~ r2_hidden(sK11(sK118,sK119),sK119) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_946,negated_conjecture,
    ( ~ r1_tarski(sK118,sK119) ),
    inference(cnf_transformation,[],[f2338])).

cnf(c_947,negated_conjecture,
    ( r1_tarski(k7_setfam_1(sK117,sK118),k7_setfam_1(sK117,sK119)) ),
    inference(cnf_transformation,[],[f2337])).

cnf(c_948,negated_conjecture,
    ( m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(cnf_transformation,[],[f2336])).

cnf(c_949,negated_conjecture,
    ( m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(cnf_transformation,[],[f2335])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_230239,c_211059,c_115760,c_112817,c_82793,c_71791,c_47446,c_47438,c_946,c_947,c_948,c_949])).

%------------------------------------------------------------------------------
