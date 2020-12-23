%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
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
%              Number of clauses        :   30 (  32 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  198 ( 260 expanded)
%              Number of equality atoms :   91 (  91 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(cc2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_xboole_0(X2)
           => ~ v1_subset_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(cc4_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

fof(c_0_18,plain,(
    ! [X75,X76] :
      ( v1_xboole_0(X75)
      | ~ v1_zfmisc_1(X75)
      | ~ m1_subset_1(X76,k1_zfmisc_1(X75))
      | v1_xboole_0(X76)
      | ~ v1_subset_1(X76,X75) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_19,plain,(
    ! [X62,X63] :
      ( ~ v1_xboole_0(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(X62))
      | ~ v1_subset_1(X63,X62) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

fof(c_0_20,plain,(
    ! [X71,X72] :
      ( v1_xboole_0(X71)
      | ~ m1_subset_1(X72,X71)
      | m1_subset_1(k6_domain_1(X71,X72),k1_zfmisc_1(X71)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & m1_subset_1(esk3_0,esk2_0)
    & v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)
    & v1_zfmisc_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X73,X74] :
      ( v1_xboole_0(X73)
      | ~ m1_subset_1(X74,X73)
      | k6_domain_1(X73,X74) = k1_tarski(X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_28,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k5_enumset1(X27,X27,X28,X29,X30,X31,X32) = k4_enumset1(X27,X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] : k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39) = k5_enumset1(X33,X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_35,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v1_zfmisc_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_40,plain,(
    ! [X64,X65] :
      ( ( ~ m1_subset_1(X64,k1_zfmisc_1(X65))
        | r1_tarski(X64,X65) )
      & ( ~ r1_tarski(X64,X65)
        | m1_subset_1(X64,k1_zfmisc_1(X65)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_41,plain,(
    ! [X61] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X61)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_42,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59] :
      ( ( ~ r2_hidden(X49,X48)
        | X49 = X40
        | X49 = X41
        | X49 = X42
        | X49 = X43
        | X49 = X44
        | X49 = X45
        | X49 = X46
        | X49 = X47
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X40
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X41
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X42
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X43
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X44
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X45
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X46
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X47
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X51
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X52
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X53
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X54
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X55
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X56
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X57
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X58
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X51
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X52
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X53
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X54
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X55
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X56
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X57
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X58
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(k6_domain_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

fof(c_0_53,plain,(
    ! [X69,X70] :
      ( ~ r2_hidden(X69,X70)
      | ~ r1_tarski(X70,X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k6_domain_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_25]),c_0_58]),c_0_26])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:54:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 0.13/0.37  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.13/0.37  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.13/0.37  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.13/0.37  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.37  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.13/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.37  fof(c_0_17, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.13/0.37  fof(c_0_18, plain, ![X75, X76]:(v1_xboole_0(X75)|~v1_zfmisc_1(X75)|(~m1_subset_1(X76,k1_zfmisc_1(X75))|(v1_xboole_0(X76)|~v1_subset_1(X76,X75)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.13/0.37  fof(c_0_19, plain, ![X62, X63]:(~v1_xboole_0(X62)|(~m1_subset_1(X63,k1_zfmisc_1(X62))|~v1_subset_1(X63,X62))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.13/0.37  fof(c_0_20, plain, ![X71, X72]:(v1_xboole_0(X71)|~m1_subset_1(X72,X71)|m1_subset_1(k6_domain_1(X71,X72),k1_zfmisc_1(X71))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.13/0.37  fof(c_0_21, negated_conjecture, (~v1_xboole_0(esk2_0)&(m1_subset_1(esk3_0,esk2_0)&(v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)&v1_zfmisc_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.37  cnf(c_0_22, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_24, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  fof(c_0_27, plain, ![X73, X74]:(v1_xboole_0(X73)|~m1_subset_1(X74,X73)|k6_domain_1(X73,X74)=k1_tarski(X74)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.37  fof(c_0_28, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_29, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_30, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_31, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_32, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.37  fof(c_0_33, plain, ![X27, X28, X29, X30, X31, X32]:k5_enumset1(X27,X27,X28,X29,X30,X31,X32)=k4_enumset1(X27,X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.37  fof(c_0_34, plain, ![X33, X34, X35, X36, X37, X38, X39]:k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39)=k5_enumset1(X33,X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.37  fof(c_0_35, plain, ![X11]:(~v1_xboole_0(X11)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.37  cnf(c_0_36, plain, (v1_xboole_0(X1)|~v1_zfmisc_1(X2)|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (m1_subset_1(k6_domain_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (v1_zfmisc_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  fof(c_0_40, plain, ![X64, X65]:((~m1_subset_1(X64,k1_zfmisc_1(X65))|r1_tarski(X64,X65))&(~r1_tarski(X64,X65)|m1_subset_1(X64,k1_zfmisc_1(X65)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.37  fof(c_0_41, plain, ![X61]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X61)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.37  fof(c_0_42, plain, ![X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59]:(((~r2_hidden(X49,X48)|(X49=X40|X49=X41|X49=X42|X49=X43|X49=X44|X49=X45|X49=X46|X49=X47)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47))&((((((((X50!=X40|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47))&(X50!=X41|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X42|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X43|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X44|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X45|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X46|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X47|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47))))&(((((((((esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X51|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X52|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X53|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X54|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X55|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X56|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X57|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X58|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X51|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X52|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X53|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X54|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X55|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X56|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X57|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X58)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.13/0.37  cnf(c_0_43, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_44, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_46, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_47, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_48, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_49, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.37  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (v1_xboole_0(k6_domain_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.13/0.37  fof(c_0_53, plain, ![X69, X70]:(~r2_hidden(X69,X70)|~r1_tarski(X70,X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.37  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.37  cnf(c_0_55, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.37  cnf(c_0_56, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.37  cnf(c_0_57, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, (k6_domain_1(esk2_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.37  cnf(c_0_59, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.37  cnf(c_0_60, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.37  cnf(c_0_61, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).
% 0.13/0.37  cnf(c_0_62, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_25]), c_0_58]), c_0_26])).
% 0.13/0.37  cnf(c_0_63, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.37  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 65
% 0.13/0.37  # Proof object clause steps            : 30
% 0.13/0.37  # Proof object formula steps           : 35
% 0.13/0.37  # Proof object conjectures             : 12
% 0.13/0.37  # Proof object clause conjectures      : 9
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 20
% 0.13/0.37  # Proof object initial formulas used   : 17
% 0.13/0.37  # Proof object generating inferences   : 7
% 0.13/0.37  # Proof object simplifying inferences  : 17
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 18
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 39
% 0.13/0.37  # Removed in clause preprocessing      : 7
% 0.13/0.37  # Initial clauses in saturation        : 32
% 0.13/0.37  # Processed clauses                    : 88
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 7
% 0.13/0.37  # ...remaining for further processing  : 81
% 0.13/0.37  # Other redundant clauses eliminated   : 17
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 5
% 0.13/0.37  # Generated clauses                    : 55
% 0.13/0.37  # ...of the previous two non-trivial   : 44
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 46
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 17
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 35
% 0.13/0.37  #    Positive orientable unit clauses  : 16
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 17
% 0.13/0.37  # Current number of unprocessed clauses: 17
% 0.13/0.37  # ...number of literals in the above   : 63
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 44
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 131
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 104
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.37  # Unit Clause-clause subsumption calls : 4
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 58
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3030
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.030 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
