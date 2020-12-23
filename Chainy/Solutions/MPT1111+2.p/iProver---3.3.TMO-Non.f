%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1111+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Timeout 59.34s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   90 ( 119 expanded)
%              Number of clauses        :   31 (  31 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  256 ( 393 expanded)
%              Number of equality atoms :   32 (  67 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1952,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f5668,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1952])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2249,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f2250,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f2249])).

fof(f6454,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2250])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8420,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f9629,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f6454,f8420])).

fof(f1815,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_hidden(X2,X1) )
              & k1_struct_0(X0) != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1816,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r2_hidden(X2,X1) )
                & k1_struct_0(X0) != X1 ) ) ) ),
    inference(negated_conjecture,[],[f1815])).

fof(f3873,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & k1_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1816])).

fof(f3874,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & k1_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3873])).

fof(f5470,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & k1_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X2] :
            ( ~ r2_hidden(X2,sK671)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & k1_struct_0(X0) != sK671
        & m1_subset_1(sK671,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f5469,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & k1_struct_0(X0) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK670)) )
          & k1_struct_0(sK670) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK670))) )
      & l1_pre_topc(sK670) ) ),
    introduced(choice_axiom,[])).

fof(f5471,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK671)
        | ~ m1_subset_1(X2,u1_struct_0(sK670)) )
    & k1_struct_0(sK670) != sK671
    & m1_subset_1(sK671,k1_zfmisc_1(u1_struct_0(sK670)))
    & l1_pre_topc(sK670) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK670,sK671])],[f3874,f5470,f5469])).

fof(f9017,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK671)
      | ~ m1_subset_1(X2,u1_struct_0(sK670)) ) ),
    inference(cnf_transformation,[],[f5471])).

fof(f655,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2303,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f655])).

fof(f4363,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2303])).

fof(f4364,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f4363])).

fof(f4365,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK189(X0,X1),sK190(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK189(X0,X1),sK190(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4366,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK189(X0,X1),sK190(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK189(X0,X1),sK190(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK189,sK190])],[f4364,f4365])).

fof(f6533,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK189(X0,X1),sK190(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f4366])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1863,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f3974,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1863])).

fof(f3975,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f3974])).

fof(f3976,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK58(X0,X1),X1)
        & r2_hidden(sK58(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3977,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK58(X0,X1),X1)
          & r2_hidden(sK58(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK58])],[f3975,f3976])).

fof(f5481,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK58(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f3977])).

fof(f1791,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3840,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1791])).

fof(f8973,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3840])).

fof(f1769,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3815,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1769])).

fof(f8937,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3815])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5479,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f10748,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f8937,f5479])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4015,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f4016,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f4015])).

fof(f5540,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4016])).

fof(f1776,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3823,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1776])).

fof(f8958,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3823])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3067,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f7566,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f3067])).

fof(f9896,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f7566,f8420])).

fof(f1248,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7617,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1248])).

fof(f9947,plain,(
    ! [X0,X1] : m1_subset_1(o_0_0_xboole_0,k9_setfam_1(k2_zfmisc_1(X0,X1))) ),
    inference(definition_unfolding,[],[f7617,f5479,f8420])).

fof(f9016,plain,(
    k1_struct_0(sK670) != sK671 ),
    inference(cnf_transformation,[],[f5471])).

fof(f9015,plain,(
    m1_subset_1(sK671,k1_zfmisc_1(u1_struct_0(sK670))) ),
    inference(cnf_transformation,[],[f5471])).

fof(f10783,plain,(
    m1_subset_1(sK671,k9_setfam_1(u1_struct_0(sK670))) ),
    inference(definition_unfolding,[],[f9015,f8420])).

fof(f9014,plain,(
    l1_pre_topc(sK670) ),
    inference(cnf_transformation,[],[f5471])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f5668])).

cnf(c_215258,plain,
    ( ~ r2_hidden(k4_tarski(sK189(k1_struct_0(sK670),sK671),sK190(k1_struct_0(sK670),sK671)),k1_struct_0(sK670))
    | ~ v1_xboole_0(k1_struct_0(sK670)) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_968,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f9629])).

cnf(c_146384,plain,
    ( m1_subset_1(X0,u1_struct_0(sK670))
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(sK670)))
    | ~ r2_hidden(X0,X1) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_163750,plain,
    ( m1_subset_1(X0,u1_struct_0(sK670))
    | ~ m1_subset_1(sK671,k9_setfam_1(u1_struct_0(sK670)))
    | ~ r2_hidden(X0,sK671) ),
    inference(instantiation,[status(thm)],[c_146384])).

cnf(c_211307,plain,
    ( m1_subset_1(sK58(sK671,k1_struct_0(sK670)),u1_struct_0(sK670))
    | ~ m1_subset_1(sK671,k9_setfam_1(u1_struct_0(sK670)))
    | ~ r2_hidden(sK58(sK671,k1_struct_0(sK670)),sK671) ),
    inference(instantiation,[status(thm)],[c_163750])).

cnf(c_3515,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK670))
    | ~ r2_hidden(X0,sK671) ),
    inference(cnf_transformation,[],[f9017])).

cnf(c_211308,plain,
    ( ~ m1_subset_1(sK58(sK671,k1_struct_0(sK670)),u1_struct_0(sK670))
    | ~ r2_hidden(sK58(sK671,k1_struct_0(sK670)),sK671) ),
    inference(instantiation,[status(thm)],[c_3515])).

cnf(c_1047,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK189(X0,X1),sK190(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f6533])).

cnf(c_161498,plain,
    ( r1_tarski(k1_struct_0(sK670),sK671)
    | r2_hidden(k4_tarski(sK189(k1_struct_0(sK670),sK671),sK190(k1_struct_0(sK670),sK671)),k1_struct_0(sK670))
    | ~ v1_relat_1(k1_struct_0(sK670)) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_50892,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_161459,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k1_struct_0(sK670))
    | k1_struct_0(sK670) != X0 ),
    inference(instantiation,[status(thm)],[c_50892])).

cnf(c_161461,plain,
    ( v1_relat_1(k1_struct_0(sK670))
    | ~ v1_relat_1(o_0_0_xboole_0)
    | k1_struct_0(sK670) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_161459])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK58(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5481])).

cnf(c_161115,plain,
    ( r1_tarski(sK671,k1_struct_0(sK670))
    | r2_hidden(sK58(sK671,k1_struct_0(sK670)),sK671) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3474,plain,
    ( ~ l1_struct_0(X0)
    | v1_xboole_0(k1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f8973])).

cnf(c_160899,plain,
    ( ~ l1_struct_0(sK670)
    | v1_xboole_0(k1_struct_0(sK670)) ),
    inference(instantiation,[status(thm)],[c_3474])).

cnf(c_3438,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f10748])).

cnf(c_160900,plain,
    ( ~ l1_struct_0(sK670)
    | k1_struct_0(sK670) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3438])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f5540])).

cnf(c_144414,plain,
    ( ~ r1_tarski(k1_struct_0(sK670),sK671)
    | ~ r1_tarski(sK671,k1_struct_0(sK670))
    | k1_struct_0(sK670) = sK671 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_3459,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f8958])).

cnf(c_134280,plain,
    ( l1_struct_0(sK670)
    | ~ l1_pre_topc(sK670) ),
    inference(instantiation,[status(thm)],[c_3459])).

cnf(c_2079,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f9896])).

cnf(c_7268,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k9_setfam_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | v1_relat_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2079])).

cnf(c_2130,plain,
    ( m1_subset_1(o_0_0_xboole_0,k9_setfam_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f9947])).

cnf(c_7149,plain,
    ( m1_subset_1(o_0_0_xboole_0,k9_setfam_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_3516,negated_conjecture,
    ( k1_struct_0(sK670) != sK671 ),
    inference(cnf_transformation,[],[f9016])).

cnf(c_3517,negated_conjecture,
    ( m1_subset_1(sK671,k9_setfam_1(u1_struct_0(sK670))) ),
    inference(cnf_transformation,[],[f10783])).

cnf(c_3518,negated_conjecture,
    ( l1_pre_topc(sK670) ),
    inference(cnf_transformation,[],[f9014])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_215258,c_211307,c_211308,c_161498,c_161461,c_161115,c_160899,c_160900,c_144414,c_134280,c_7268,c_7149,c_3516,c_3517,c_3518])).

%------------------------------------------------------------------------------
