%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:05 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   62 (  79 expanded)
%              Number of clauses        :   29 (  31 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  196 ( 258 expanded)
%              Number of equality atoms :  104 ( 104 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(cc2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_xboole_0(X2)
           => ~ v1_subset_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(cc4_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

fof(c_0_17,plain,(
    ! [X71,X72] :
      ( v1_xboole_0(X71)
      | ~ v1_zfmisc_1(X71)
      | ~ m1_subset_1(X72,k1_zfmisc_1(X71))
      | v1_xboole_0(X72)
      | ~ v1_subset_1(X72,X71) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_18,plain,(
    ! [X65,X66] :
      ( ~ v1_xboole_0(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(X65))
      | ~ v1_subset_1(X66,X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

fof(c_0_19,plain,(
    ! [X67,X68] :
      ( v1_xboole_0(X67)
      | ~ m1_subset_1(X68,X67)
      | m1_subset_1(k6_domain_1(X67,X68),k1_zfmisc_1(X67)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & m1_subset_1(esk3_0,esk2_0)
    & v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)
    & v1_zfmisc_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X69,X70] :
      ( v1_xboole_0(X69)
      | ~ m1_subset_1(X70,X69)
      | k6_domain_1(X69,X70) = k1_tarski(X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_27,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_28,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_32,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k5_enumset1(X27,X27,X28,X29,X30,X31,X32) = k4_enumset1(X27,X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_33,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] : k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39) = k5_enumset1(X33,X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_34,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( v1_zfmisc_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_39,plain,(
    ! [X40,X41] :
      ( ( k2_zfmisc_1(X40,X41) != k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0 )
      & ( X40 != k1_xboole_0
        | k2_zfmisc_1(X40,X41) = k1_xboole_0 )
      & ( X41 != k1_xboole_0
        | k2_zfmisc_1(X40,X41) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_40,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63] :
      ( ( ~ r2_hidden(X53,X52)
        | X53 = X44
        | X53 = X45
        | X53 = X46
        | X53 = X47
        | X53 = X48
        | X53 = X49
        | X53 = X50
        | X53 = X51
        | X52 != k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) )
      & ( X54 != X44
        | r2_hidden(X54,X52)
        | X52 != k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) )
      & ( X54 != X45
        | r2_hidden(X54,X52)
        | X52 != k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) )
      & ( X54 != X46
        | r2_hidden(X54,X52)
        | X52 != k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) )
      & ( X54 != X47
        | r2_hidden(X54,X52)
        | X52 != k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) )
      & ( X54 != X48
        | r2_hidden(X54,X52)
        | X52 != k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) )
      & ( X54 != X49
        | r2_hidden(X54,X52)
        | X52 != k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) )
      & ( X54 != X50
        | r2_hidden(X54,X52)
        | X52 != k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) )
      & ( X54 != X51
        | r2_hidden(X54,X52)
        | X52 != k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) )
      & ( esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) != X55
        | ~ r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)
        | X63 = k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) != X56
        | ~ r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)
        | X63 = k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) != X57
        | ~ r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)
        | X63 = k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) != X58
        | ~ r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)
        | X63 = k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) != X59
        | ~ r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)
        | X63 = k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) != X60
        | ~ r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)
        | X63 = k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) != X61
        | ~ r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)
        | X63 = k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) != X62
        | ~ r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)
        | X63 = k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)
        | esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) = X55
        | esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) = X56
        | esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) = X57
        | esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) = X58
        | esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) = X59
        | esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) = X60
        | esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) = X61
        | esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63) = X62
        | X63 = k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(k6_domain_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

fof(c_0_51,plain,(
    ! [X42,X43] : ~ r2_hidden(X42,k2_zfmisc_1(X42,X43)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k6_domain_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_24]),c_0_55]),c_0_25])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:18:06 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  # Version: 2.5pre002
% 0.15/0.34  # No SInE strategy applied
% 0.15/0.34  # Trying AutoSched0 for 299 seconds
% 0.15/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.15/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.15/0.37  #
% 0.15/0.37  # Preprocessing time       : 0.028 s
% 0.15/0.37  # Presaturation interreduction done
% 0.15/0.37  
% 0.15/0.37  # Proof found!
% 0.15/0.37  # SZS status Theorem
% 0.15/0.37  # SZS output start CNFRefutation
% 0.15/0.37  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.15/0.37  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.15/0.37  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.15/0.37  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.15/0.37  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.15/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.15/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.15/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.15/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.15/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.15/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.15/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.15/0.37  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.15/0.37  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.15/0.37  fof(c_0_16, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.15/0.37  fof(c_0_17, plain, ![X71, X72]:(v1_xboole_0(X71)|~v1_zfmisc_1(X71)|(~m1_subset_1(X72,k1_zfmisc_1(X71))|(v1_xboole_0(X72)|~v1_subset_1(X72,X71)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.15/0.37  fof(c_0_18, plain, ![X65, X66]:(~v1_xboole_0(X65)|(~m1_subset_1(X66,k1_zfmisc_1(X65))|~v1_subset_1(X66,X65))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.15/0.37  fof(c_0_19, plain, ![X67, X68]:(v1_xboole_0(X67)|~m1_subset_1(X68,X67)|m1_subset_1(k6_domain_1(X67,X68),k1_zfmisc_1(X67))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.15/0.37  fof(c_0_20, negated_conjecture, (~v1_xboole_0(esk2_0)&(m1_subset_1(esk3_0,esk2_0)&(v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)&v1_zfmisc_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.15/0.37  cnf(c_0_21, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.37  cnf(c_0_22, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.37  cnf(c_0_23, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.37  cnf(c_0_25, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.37  fof(c_0_26, plain, ![X69, X70]:(v1_xboole_0(X69)|~m1_subset_1(X70,X69)|k6_domain_1(X69,X70)=k1_tarski(X70)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.15/0.37  fof(c_0_27, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.37  fof(c_0_28, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.15/0.37  fof(c_0_29, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.15/0.37  fof(c_0_30, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.15/0.37  fof(c_0_31, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.15/0.37  fof(c_0_32, plain, ![X27, X28, X29, X30, X31, X32]:k5_enumset1(X27,X27,X28,X29,X30,X31,X32)=k4_enumset1(X27,X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.15/0.37  fof(c_0_33, plain, ![X33, X34, X35, X36, X37, X38, X39]:k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39)=k5_enumset1(X33,X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.15/0.37  fof(c_0_34, plain, ![X11]:(~v1_xboole_0(X11)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.15/0.37  cnf(c_0_35, plain, (v1_xboole_0(X1)|~v1_zfmisc_1(X2)|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.15/0.37  cnf(c_0_36, negated_conjecture, (m1_subset_1(k6_domain_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.15/0.37  cnf(c_0_37, negated_conjecture, (v1_zfmisc_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.37  cnf(c_0_38, negated_conjecture, (v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.37  fof(c_0_39, plain, ![X40, X41]:((k2_zfmisc_1(X40,X41)!=k1_xboole_0|(X40=k1_xboole_0|X41=k1_xboole_0))&((X40!=k1_xboole_0|k2_zfmisc_1(X40,X41)=k1_xboole_0)&(X41!=k1_xboole_0|k2_zfmisc_1(X40,X41)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.15/0.37  fof(c_0_40, plain, ![X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63]:(((~r2_hidden(X53,X52)|(X53=X44|X53=X45|X53=X46|X53=X47|X53=X48|X53=X49|X53=X50|X53=X51)|X52!=k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51))&((((((((X54!=X44|r2_hidden(X54,X52)|X52!=k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51))&(X54!=X45|r2_hidden(X54,X52)|X52!=k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51)))&(X54!=X46|r2_hidden(X54,X52)|X52!=k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51)))&(X54!=X47|r2_hidden(X54,X52)|X52!=k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51)))&(X54!=X48|r2_hidden(X54,X52)|X52!=k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51)))&(X54!=X49|r2_hidden(X54,X52)|X52!=k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51)))&(X54!=X50|r2_hidden(X54,X52)|X52!=k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51)))&(X54!=X51|r2_hidden(X54,X52)|X52!=k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51))))&(((((((((esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)!=X55|~r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)|X63=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62))&(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)!=X56|~r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)|X63=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)!=X57|~r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)|X63=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)!=X58|~r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)|X63=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)!=X59|~r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)|X63=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)!=X60|~r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)|X63=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)!=X61|~r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)|X63=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)!=X62|~r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)|X63=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(r2_hidden(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63),X63)|(esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)=X55|esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)=X56|esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)=X57|esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)=X58|esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)=X59|esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)=X60|esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)=X61|esk1_9(X55,X56,X57,X58,X59,X60,X61,X62,X63)=X62)|X63=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.15/0.37  cnf(c_0_41, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.15/0.37  cnf(c_0_42, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.37  cnf(c_0_43, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.15/0.37  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.37  cnf(c_0_45, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.15/0.37  cnf(c_0_46, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.15/0.37  cnf(c_0_47, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.15/0.37  cnf(c_0_48, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.15/0.37  cnf(c_0_49, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.15/0.37  cnf(c_0_50, negated_conjecture, (v1_xboole_0(k6_domain_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 0.15/0.37  fof(c_0_51, plain, ![X42, X43]:~r2_hidden(X42,k2_zfmisc_1(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.15/0.37  cnf(c_0_52, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.15/0.37  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.37  cnf(c_0_54, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48])).
% 0.15/0.37  cnf(c_0_55, negated_conjecture, (k6_domain_1(esk2_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.15/0.37  cnf(c_0_56, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.37  cnf(c_0_57, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_52])).
% 0.15/0.37  cnf(c_0_58, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).
% 0.15/0.37  cnf(c_0_59, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_24]), c_0_55]), c_0_25])).
% 0.15/0.37  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.15/0.37  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), ['proof']).
% 0.15/0.37  # SZS output end CNFRefutation
% 0.15/0.37  # Proof object total steps             : 62
% 0.15/0.37  # Proof object clause steps            : 29
% 0.15/0.37  # Proof object formula steps           : 33
% 0.15/0.37  # Proof object conjectures             : 12
% 0.15/0.37  # Proof object clause conjectures      : 9
% 0.15/0.37  # Proof object formula conjectures     : 3
% 0.15/0.37  # Proof object initial clauses used    : 19
% 0.15/0.37  # Proof object initial formulas used   : 16
% 0.15/0.37  # Proof object generating inferences   : 6
% 0.15/0.37  # Proof object simplifying inferences  : 18
% 0.15/0.37  # Training examples: 0 positive, 0 negative
% 0.15/0.37  # Parsed axioms                        : 16
% 0.15/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.37  # Initial clauses                      : 38
% 0.15/0.37  # Removed in clause preprocessing      : 7
% 0.15/0.37  # Initial clauses in saturation        : 31
% 0.15/0.37  # Processed clauses                    : 84
% 0.15/0.37  # ...of these trivial                  : 1
% 0.15/0.37  # ...subsumed                          : 6
% 0.15/0.37  # ...remaining for further processing  : 77
% 0.15/0.37  # Other redundant clauses eliminated   : 21
% 0.15/0.37  # Clauses deleted for lack of memory   : 0
% 0.15/0.37  # Backward-subsumed                    : 0
% 0.15/0.37  # Backward-rewritten                   : 3
% 0.15/0.37  # Generated clauses                    : 50
% 0.15/0.37  # ...of the previous two non-trivial   : 36
% 0.15/0.37  # Contextual simplify-reflections      : 1
% 0.15/0.37  # Paramodulations                      : 29
% 0.15/0.37  # Factorizations                       : 8
% 0.15/0.37  # Equation resolutions                 : 21
% 0.15/0.37  # Propositional unsat checks           : 0
% 0.15/0.37  #    Propositional check models        : 0
% 0.15/0.37  #    Propositional check unsatisfiable : 0
% 0.15/0.37  #    Propositional clauses             : 0
% 0.15/0.37  #    Propositional clauses after purity: 0
% 0.15/0.37  #    Propositional unsat core size     : 0
% 0.15/0.37  #    Propositional preprocessing time  : 0.000
% 0.15/0.37  #    Propositional encoding time       : 0.000
% 0.15/0.37  #    Propositional solver time         : 0.000
% 0.15/0.37  #    Success case prop preproc time    : 0.000
% 0.15/0.37  #    Success case prop encoding time   : 0.000
% 0.15/0.37  #    Success case prop solver time     : 0.000
% 0.15/0.37  # Current number of processed clauses  : 32
% 0.15/0.37  #    Positive orientable unit clauses  : 17
% 0.15/0.37  #    Positive unorientable unit clauses: 0
% 0.15/0.37  #    Negative unit clauses             : 3
% 0.15/0.37  #    Non-unit-clauses                  : 12
% 0.15/0.37  # Current number of unprocessed clauses: 13
% 0.15/0.37  # ...number of literals in the above   : 53
% 0.15/0.37  # Current number of archived formulas  : 0
% 0.15/0.37  # Current number of archived clauses   : 41
% 0.15/0.37  # Clause-clause subsumption calls (NU) : 84
% 0.15/0.37  # Rec. Clause-clause subsumption calls : 74
% 0.15/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.15/0.37  # Unit Clause-clause subsumption calls : 1
% 0.15/0.37  # Rewrite failures with RHS unbound    : 0
% 0.15/0.37  # BW rewrite match attempts            : 57
% 0.15/0.37  # BW rewrite match successes           : 1
% 0.15/0.37  # Condensation attempts                : 0
% 0.15/0.37  # Condensation successes               : 0
% 0.15/0.37  # Termbank termtop insertions          : 2786
% 0.15/0.38  
% 0.15/0.38  # -------------------------------------------------
% 0.15/0.38  # User time                : 0.030 s
% 0.15/0.38  # System time              : 0.005 s
% 0.15/0.38  # Total time               : 0.035 s
% 0.15/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
