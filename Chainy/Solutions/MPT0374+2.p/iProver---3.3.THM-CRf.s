%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0374+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:37 EST 2020

% Result     : Theorem 35.12s
% Output     : CNFRefutation 35.12s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 127 expanded)
%              Number of clauses        :   25 (  29 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  221 ( 392 expanded)
%              Number of equality atoms :   44 (  87 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f455,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f765,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f455])).

fof(f1044,plain,(
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
    inference(nnf_transformation,[],[f765])).

fof(f1762,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1044])).

fof(f396,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1013,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f396])).

fof(f1014,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f1013])).

fof(f1666,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1014])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1410,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1314,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1254,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1864,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1314,f1254])).

fof(f1865,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f1410,f1864])).

fof(f2211,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f1666,f1865])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1311,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1103,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f937,plain,(
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

fof(f938,plain,(
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
    inference(rectify,[],[f937])).

fof(f939,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK24(X0,X1),X0)
          | ~ r2_hidden(sK24(X0,X1),X1) )
        & ( r1_tarski(sK24(X0,X1),X0)
          | r2_hidden(sK24(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f940,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK24(X0,X1),X0)
            | ~ r2_hidden(sK24(X0,X1),X1) )
          & ( r1_tarski(sK24(X0,X1),X0)
            | r2_hidden(sK24(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f938,f939])).

fof(f1469,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f940])).

fof(f2349,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f1469])).

fof(f1763,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1044])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f625,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f1295,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f625])).

fof(f160,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f634,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f160])).

fof(f1308,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f634])).

fof(f516,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f517,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f516])).

fof(f835,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f517])).

fof(f836,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f835])).

fof(f1091,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
     => ( ~ m1_subset_1(k2_tarski(X1,sK78),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK78,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1090,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(sK77,X2),k1_zfmisc_1(sK76))
          & k1_xboole_0 != sK76
          & m1_subset_1(X2,sK76) )
      & m1_subset_1(sK77,sK76) ) ),
    introduced(choice_axiom,[])).

fof(f1092,plain,
    ( ~ m1_subset_1(k2_tarski(sK77,sK78),k1_zfmisc_1(sK76))
    & k1_xboole_0 != sK76
    & m1_subset_1(sK78,sK76)
    & m1_subset_1(sK77,sK76) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK76,sK77,sK78])],[f836,f1091,f1090])).

fof(f1857,plain,(
    ~ m1_subset_1(k2_tarski(sK77,sK78),k1_zfmisc_1(sK76)) ),
    inference(cnf_transformation,[],[f1092])).

fof(f2297,plain,(
    ~ m1_subset_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK77),k1_tarski(sK78)),k4_xboole_0(k1_tarski(sK77),k4_xboole_0(k1_tarski(sK77),k1_tarski(sK78)))),k1_zfmisc_1(sK76)) ),
    inference(definition_unfolding,[],[f1857,f1865])).

fof(f470,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1779,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f470])).

fof(f456,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1766,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f456])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1106,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1874,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f1766,f1106])).

fof(f2281,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f1779,f1874])).

fof(f1856,plain,(
    k1_xboole_0 != sK76 ),
    inference(cnf_transformation,[],[f1092])).

fof(f2298,plain,(
    o_0_0_xboole_0 != sK76 ),
    inference(definition_unfolding,[],[f1856,f1106])).

fof(f1855,plain,(
    m1_subset_1(sK78,sK76) ),
    inference(cnf_transformation,[],[f1092])).

fof(f1854,plain,(
    m1_subset_1(sK77,sK76) ),
    inference(cnf_transformation,[],[f1092])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1762])).

cnf(c_25988,plain,
    ( ~ m1_subset_1(X0,sK76)
    | r2_hidden(X0,sK76)
    | v1_xboole_0(sK76) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_99158,plain,
    ( ~ m1_subset_1(sK77,sK76)
    | r2_hidden(sK77,sK76)
    | v1_xboole_0(sK76) ),
    inference(instantiation,[status(thm)],[c_25988])).

cnf(c_99155,plain,
    ( ~ m1_subset_1(sK78,sK76)
    | r2_hidden(sK78,sK76)
    | v1_xboole_0(sK76) ),
    inference(instantiation,[status(thm)],[c_25988])).

cnf(c_553,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f2211])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1311])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1103])).

cnf(c_12867,plain,
    ( r1_tarski(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(theory_normalisation,[status(thm)],[c_553,c_211,c_7])).

cnf(c_54761,plain,
    ( r1_tarski(k5_xboole_0(k1_tarski(sK77),k5_xboole_0(k1_tarski(sK78),k4_xboole_0(k1_tarski(sK77),k4_xboole_0(k1_tarski(sK77),k1_tarski(sK78))))),sK76)
    | ~ r2_hidden(sK78,sK76)
    | ~ r2_hidden(sK77,sK76) ),
    inference(instantiation,[status(thm)],[c_12867])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f2349])).

cnf(c_26535,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_tarski(sK77),k5_xboole_0(k1_tarski(sK78),k4_xboole_0(k1_tarski(sK77),k4_xboole_0(k1_tarski(sK77),k1_tarski(sK78))))),sK76)
    | r2_hidden(k5_xboole_0(k1_tarski(sK77),k5_xboole_0(k1_tarski(sK78),k4_xboole_0(k1_tarski(sK77),k4_xboole_0(k1_tarski(sK77),k1_tarski(sK78))))),k1_zfmisc_1(sK76)) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_653,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1763])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1295])).

cnf(c_3246,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_195])).

cnf(c_3247,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_3246])).

cnf(c_23951,plain,
    ( m1_subset_1(k5_xboole_0(k1_tarski(sK77),k5_xboole_0(k1_tarski(sK78),k4_xboole_0(k1_tarski(sK77),k4_xboole_0(k1_tarski(sK77),k1_tarski(sK78))))),k1_zfmisc_1(sK76))
    | ~ r2_hidden(k5_xboole_0(k1_tarski(sK77),k5_xboole_0(k1_tarski(sK78),k4_xboole_0(k1_tarski(sK77),k4_xboole_0(k1_tarski(sK77),k1_tarski(sK78))))),k1_zfmisc_1(sK76)) ),
    inference(instantiation,[status(thm)],[c_3247])).

cnf(c_208,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1308])).

cnf(c_23605,plain,
    ( ~ v1_xboole_0(sK76)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK76 ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_741,negated_conjecture,
    ( ~ m1_subset_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK77),k1_tarski(sK78)),k4_xboole_0(k1_tarski(sK77),k4_xboole_0(k1_tarski(sK77),k1_tarski(sK78)))),k1_zfmisc_1(sK76)) ),
    inference(cnf_transformation,[],[f2297])).

cnf(c_12830,negated_conjecture,
    ( ~ m1_subset_1(k5_xboole_0(k1_tarski(sK77),k5_xboole_0(k1_tarski(sK78),k4_xboole_0(k1_tarski(sK77),k4_xboole_0(k1_tarski(sK77),k1_tarski(sK78))))),k1_zfmisc_1(sK76)) ),
    inference(theory_normalisation,[status(thm)],[c_741,c_211,c_7])).

cnf(c_667,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2281])).

cnf(c_742,negated_conjecture,
    ( o_0_0_xboole_0 != sK76 ),
    inference(cnf_transformation,[],[f2298])).

cnf(c_743,negated_conjecture,
    ( m1_subset_1(sK78,sK76) ),
    inference(cnf_transformation,[],[f1855])).

cnf(c_744,negated_conjecture,
    ( m1_subset_1(sK77,sK76) ),
    inference(cnf_transformation,[],[f1854])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99158,c_99155,c_54761,c_26535,c_23951,c_23605,c_12830,c_667,c_742,c_743,c_744])).

%------------------------------------------------------------------------------
