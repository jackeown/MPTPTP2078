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

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   65 (  82 expanded)
%              Number of clauses        :   31 (  33 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  203 ( 265 expanded)
%              Number of equality atoms :  105 ( 105 expanded)
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

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

fof(c_0_18,plain,(
    ! [X72,X73] :
      ( v1_xboole_0(X72)
      | ~ v1_zfmisc_1(X72)
      | ~ m1_subset_1(X73,k1_zfmisc_1(X72))
      | v1_xboole_0(X73)
      | ~ v1_subset_1(X73,X72) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_19,plain,(
    ! [X66,X67] :
      ( ~ v1_xboole_0(X66)
      | ~ m1_subset_1(X67,k1_zfmisc_1(X66))
      | ~ v1_subset_1(X67,X66) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

fof(c_0_20,plain,(
    ! [X68,X69] :
      ( v1_xboole_0(X68)
      | ~ m1_subset_1(X69,X68)
      | m1_subset_1(k6_domain_1(X68,X69),k1_zfmisc_1(X68)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & m1_subset_1(esk3_0,esk2_0)
    & v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)
    & v1_zfmisc_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | X11 = X12
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X70,X71] :
      ( v1_xboole_0(X70)
      | ~ m1_subset_1(X71,X70)
      | k6_domain_1(X70,X71) = k1_tarski(X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_29,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_30,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_31,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40) = k5_enumset1(X34,X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( v1_zfmisc_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_42,plain,(
    ! [X41,X42] :
      ( ( k2_zfmisc_1(X41,X42) != k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 )
      & ( X41 != k1_xboole_0
        | k2_zfmisc_1(X41,X42) = k1_xboole_0 )
      & ( X42 != k1_xboole_0
        | k2_zfmisc_1(X41,X42) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_43,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64] :
      ( ( ~ r2_hidden(X54,X53)
        | X54 = X45
        | X54 = X46
        | X54 = X47
        | X54 = X48
        | X54 = X49
        | X54 = X50
        | X54 = X51
        | X54 = X52
        | X53 != k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X45
        | r2_hidden(X55,X53)
        | X53 != k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X46
        | r2_hidden(X55,X53)
        | X53 != k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X47
        | r2_hidden(X55,X53)
        | X53 != k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X48
        | r2_hidden(X55,X53)
        | X53 != k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X49
        | r2_hidden(X55,X53)
        | X53 != k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X50
        | r2_hidden(X55,X53)
        | X53 != k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X51
        | r2_hidden(X55,X53)
        | X53 != k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X52
        | r2_hidden(X55,X53)
        | X53 != k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) != X56
        | ~ r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)
        | X64 = k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63) )
      & ( esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) != X57
        | ~ r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)
        | X64 = k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63) )
      & ( esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) != X58
        | ~ r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)
        | X64 = k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63) )
      & ( esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) != X59
        | ~ r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)
        | X64 = k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63) )
      & ( esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) != X60
        | ~ r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)
        | X64 = k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63) )
      & ( esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) != X61
        | ~ r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)
        | X64 = k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63) )
      & ( esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) != X62
        | ~ r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)
        | X64 = k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63) )
      & ( esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) != X63
        | ~ r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)
        | X64 = k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63) )
      & ( r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)
        | esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) = X56
        | esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) = X57
        | esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) = X58
        | esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) = X59
        | esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) = X60
        | esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) = X61
        | esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) = X62
        | esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64) = X63
        | X64 = k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(k6_domain_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

fof(c_0_54,plain,(
    ! [X43,X44] : ~ r2_hidden(X43,k2_zfmisc_1(X43,X44)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k6_domain_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_26]),c_0_58]),c_0_27])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:00:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.13/0.38  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.13/0.38  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.13/0.38  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.13/0.38  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.13/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.38  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.13/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.13/0.38  fof(c_0_18, plain, ![X72, X73]:(v1_xboole_0(X72)|~v1_zfmisc_1(X72)|(~m1_subset_1(X73,k1_zfmisc_1(X72))|(v1_xboole_0(X73)|~v1_subset_1(X73,X72)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X66, X67]:(~v1_xboole_0(X66)|(~m1_subset_1(X67,k1_zfmisc_1(X66))|~v1_subset_1(X67,X66))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X68, X69]:(v1_xboole_0(X68)|~m1_subset_1(X69,X68)|m1_subset_1(k6_domain_1(X68,X69),k1_zfmisc_1(X68))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.13/0.38  fof(c_0_21, negated_conjecture, (~v1_xboole_0(esk2_0)&(m1_subset_1(esk3_0,esk2_0)&(v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)&v1_zfmisc_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X11, X12]:(~v1_xboole_0(X11)|X11=X12|~v1_xboole_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.13/0.38  cnf(c_0_23, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_24, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_25, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_28, plain, ![X70, X71]:(v1_xboole_0(X70)|~m1_subset_1(X71,X70)|k6_domain_1(X70,X71)=k1_tarski(X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.38  fof(c_0_29, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_30, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_31, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_32, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_33, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  fof(c_0_34, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_35, plain, ![X34, X35, X36, X37, X38, X39, X40]:k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40)=k5_enumset1(X34,X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.38  cnf(c_0_36, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_37, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.38  cnf(c_0_38, plain, (v1_xboole_0(X1)|~v1_zfmisc_1(X2)|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(k6_domain_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (v1_zfmisc_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_42, plain, ![X41, X42]:((k2_zfmisc_1(X41,X42)!=k1_xboole_0|(X41=k1_xboole_0|X42=k1_xboole_0))&((X41!=k1_xboole_0|k2_zfmisc_1(X41,X42)=k1_xboole_0)&(X42!=k1_xboole_0|k2_zfmisc_1(X41,X42)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_43, plain, ![X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64]:(((~r2_hidden(X54,X53)|(X54=X45|X54=X46|X54=X47|X54=X48|X54=X49|X54=X50|X54=X51|X54=X52)|X53!=k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52))&((((((((X55!=X45|r2_hidden(X55,X53)|X53!=k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52))&(X55!=X46|r2_hidden(X55,X53)|X53!=k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X47|r2_hidden(X55,X53)|X53!=k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X48|r2_hidden(X55,X53)|X53!=k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X49|r2_hidden(X55,X53)|X53!=k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X50|r2_hidden(X55,X53)|X53!=k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X51|r2_hidden(X55,X53)|X53!=k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X52|r2_hidden(X55,X53)|X53!=k6_enumset1(X45,X46,X47,X48,X49,X50,X51,X52))))&(((((((((esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)!=X56|~r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)|X64=k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63))&(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)!=X57|~r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)|X64=k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)))&(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)!=X58|~r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)|X64=k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)))&(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)!=X59|~r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)|X64=k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)))&(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)!=X60|~r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)|X64=k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)))&(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)!=X61|~r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)|X64=k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)))&(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)!=X62|~r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)|X64=k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)))&(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)!=X63|~r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)|X64=k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)))&(r2_hidden(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64),X64)|(esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)=X56|esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)=X57|esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)=X58|esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)=X59|esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)=X60|esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)=X61|esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)=X62|esk1_9(X56,X57,X58,X59,X60,X61,X62,X63,X64)=X63)|X64=k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.13/0.38  cnf(c_0_44, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_45, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_46, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_47, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_48, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_49, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_50, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_51, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_52, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (v1_xboole_0(k6_domain_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])])).
% 0.13/0.38  fof(c_0_54, plain, ![X43, X44]:~r2_hidden(X43,k2_zfmisc_1(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_55, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_56, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_57, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (k6_domain_1(esk2_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_59, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.38  cnf(c_0_60, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_55])).
% 0.13/0.38  cnf(c_0_61, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_26]), c_0_58]), c_0_27])).
% 0.13/0.38  cnf(c_0_63, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 65
% 0.13/0.38  # Proof object clause steps            : 31
% 0.13/0.38  # Proof object formula steps           : 34
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 20
% 0.13/0.38  # Proof object initial formulas used   : 17
% 0.13/0.38  # Proof object generating inferences   : 7
% 0.13/0.38  # Proof object simplifying inferences  : 18
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 17
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 39
% 0.13/0.38  # Removed in clause preprocessing      : 7
% 0.13/0.38  # Initial clauses in saturation        : 32
% 0.13/0.38  # Processed clauses                    : 85
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 6
% 0.13/0.38  # ...remaining for further processing  : 78
% 0.13/0.38  # Other redundant clauses eliminated   : 21
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 52
% 0.13/0.38  # ...of the previous two non-trivial   : 37
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 31
% 0.13/0.38  # Factorizations                       : 8
% 0.13/0.38  # Equation resolutions                 : 21
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 32
% 0.13/0.38  #    Positive orientable unit clauses  : 17
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 12
% 0.13/0.38  # Current number of unprocessed clauses: 14
% 0.13/0.38  # ...number of literals in the above   : 56
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 42
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 89
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 70
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 57
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2844
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
