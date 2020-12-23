%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 797 expanded)
%              Number of clauses        :   71 ( 383 expanded)
%              Number of leaves         :   17 ( 216 expanded)
%              Depth                    :   25
%              Number of atoms          :  299 (2973 expanded)
%              Number of equality atoms :  110 (1441 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X6 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X6 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_mcart_1])).

fof(c_0_18,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | ~ r2_hidden(X48,X49)
      | X48 = k4_tarski(k1_mcart_1(X48),k2_mcart_1(X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_19,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X25,X26)
      | v1_xboole_0(X26)
      | r2_hidden(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_20,negated_conjecture,(
    ! [X65,X66,X67] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X65,esk4_0)
        | ~ m1_subset_1(X66,esk5_0)
        | ~ m1_subset_1(X67,esk6_0)
        | esk8_0 != k3_mcart_1(X65,X66,X67)
        | esk7_0 = X65 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

fof(c_0_21,plain,(
    ! [X34,X35,X36] : k3_zfmisc_1(X34,X35,X36) = k2_zfmisc_1(k2_zfmisc_1(X34,X35),X36) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X19,X20),k2_zfmisc_1(X21,X22)) )
      & ( r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X19,X20),k2_zfmisc_1(X21,X22)) )
      & ( ~ r2_hidden(X19,X21)
        | ~ r2_hidden(X20,X22)
        | r2_hidden(k4_tarski(X19,X20),k2_zfmisc_1(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_24,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X27,X28] : v1_relat_1(k2_zfmisc_1(X27,X28)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | v1_xboole_0(X2)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ v1_xboole_0(k2_zfmisc_1(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

fof(c_0_36,plain,(
    ! [X50,X52,X53,X54,X55] :
      ( ( r2_hidden(esk3_1(X50),X50)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X52,X50)
        | esk3_1(X50) != k4_mcart_1(X52,X53,X54,X55)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X53,X50)
        | esk3_1(X50) != k4_mcart_1(X52,X53,X54,X55)
        | X50 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0
    | ~ r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X3,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_42,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( esk5_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_39])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(k4_tarski(X1,X4),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_42]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),X1)
    | v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ m1_subset_1(esk8_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_32])).

fof(c_0_55,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_54])).

cnf(c_0_57,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_58,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ r1_tarski(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),X1)
    | r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),X1)
    | r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_42]),c_0_43])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_64,plain,(
    ! [X56,X57,X58,X59] :
      ( ( k5_mcart_1(X56,X57,X58,X59) = k1_mcart_1(k1_mcart_1(X59))
        | ~ m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 )
      & ( k6_mcart_1(X56,X57,X58,X59) = k2_mcart_1(k1_mcart_1(X59))
        | ~ m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 )
      & ( k7_mcart_1(X56,X57,X58,X59) = k2_mcart_1(X59)
        | ~ m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_30])).

fof(c_0_66,plain,(
    ! [X45,X46,X47] :
      ( ( r2_hidden(k1_mcart_1(X45),X46)
        | ~ r2_hidden(X45,k2_zfmisc_1(X46,X47)) )
      & ( r2_hidden(k2_mcart_1(X45),X47)
        | ~ r2_hidden(X45,k2_zfmisc_1(X46,X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))
    | v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_63])).

fof(c_0_68,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
      | m1_subset_1(k5_mcart_1(X37,X38,X39,X40),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_69,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_42]),c_0_46])).

fof(c_0_71,plain,(
    ! [X23,X24] :
      ( ~ r2_hidden(X23,X24)
      | m1_subset_1(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_72,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))
    | v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_42]),c_0_43])).

cnf(c_0_74,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_27])).

fof(c_0_76,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ m1_subset_1(X44,k3_zfmisc_1(X41,X42,X43))
      | m1_subset_1(k7_mcart_1(X41,X42,X43,X44),X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

cnf(c_0_77,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_78,plain,(
    ! [X31,X32,X33] : k3_mcart_1(X31,X32,X33) = k4_tarski(k4_tarski(X31,X32),X33) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_42]),c_0_50])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk8_0)),esk5_0)
    | v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_27])).

cnf(c_0_83,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X3 = o_0_0_xboole_0
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_84,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_85,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_27])).

cnf(c_0_86,negated_conjecture,
    ( esk7_0 = X1
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_87,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk8_0)),k2_mcart_1(k1_mcart_1(esk8_0))) = k1_mcart_1(esk8_0)
    | v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_73]),c_0_33])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_79])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk8_0)),esk5_0)
    | v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_91,plain,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X3 = o_0_0_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(X4)),X1)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_92,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_27])).

cnf(c_0_93,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X3 = o_0_0_xboole_0
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_94,negated_conjecture,
    ( esk7_0 = X1
    | esk8_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk8_0)),k2_mcart_1(k1_mcart_1(esk8_0))) = k1_mcart_1(esk8_0) ),
    inference(sr,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk8_0)),esk5_0) ),
    inference(sr,[status(thm)],[c_0_90,c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk8_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_32]),c_0_50]),c_0_46]),c_0_43])).

cnf(c_0_98,plain,
    ( X1 = o_0_0_xboole_0
    | X2 = o_0_0_xboole_0
    | X3 = o_0_0_xboole_0
    | m1_subset_1(k2_mcart_1(X4),X3)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( esk7_0 = k1_mcart_1(k1_mcart_1(esk8_0))
    | k4_tarski(k1_mcart_1(esk8_0),X1) != esk8_0
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_97])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk8_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_32]),c_0_50]),c_0_46]),c_0_43])).

cnf(c_0_101,negated_conjecture,
    ( esk7_0 != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_102,negated_conjecture,
    ( esk7_0 = k1_mcart_1(k1_mcart_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_52])])).

cnf(c_0_103,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) != k1_mcart_1(k1_mcart_1(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_83]),c_0_32])]),c_0_43]),c_0_46]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.028 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.20/0.47  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.20/0.47  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.47  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.47  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.47  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.20/0.47  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.47  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.20/0.47  fof(d2_xboole_0, axiom, k1_xboole_0=o_0_0_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 0.20/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.47  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.47  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.20/0.47  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.20/0.47  fof(dt_k5_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 0.20/0.47  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.47  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 0.20/0.47  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.47  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.20/0.47  fof(c_0_18, plain, ![X48, X49]:(~v1_relat_1(X49)|(~r2_hidden(X48,X49)|X48=k4_tarski(k1_mcart_1(X48),k2_mcart_1(X48)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.20/0.47  fof(c_0_19, plain, ![X25, X26]:(~m1_subset_1(X25,X26)|(v1_xboole_0(X26)|r2_hidden(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.47  fof(c_0_20, negated_conjecture, ![X65, X66, X67]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X65,esk4_0)|(~m1_subset_1(X66,esk5_0)|(~m1_subset_1(X67,esk6_0)|(esk8_0!=k3_mcart_1(X65,X66,X67)|esk7_0=X65))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.20/0.47  fof(c_0_21, plain, ![X34, X35, X36]:k3_zfmisc_1(X34,X35,X36)=k2_zfmisc_1(k2_zfmisc_1(X34,X35),X36), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.47  fof(c_0_22, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.47  fof(c_0_23, plain, ![X19, X20, X21, X22]:(((r2_hidden(X19,X21)|~r2_hidden(k4_tarski(X19,X20),k2_zfmisc_1(X21,X22)))&(r2_hidden(X20,X22)|~r2_hidden(k4_tarski(X19,X20),k2_zfmisc_1(X21,X22))))&(~r2_hidden(X19,X21)|~r2_hidden(X20,X22)|r2_hidden(k4_tarski(X19,X20),k2_zfmisc_1(X21,X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.20/0.47  cnf(c_0_24, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_25, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.47  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  cnf(c_0_27, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  fof(c_0_28, plain, ![X27, X28]:v1_relat_1(k2_zfmisc_1(X27,X28)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.47  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_31, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|v1_xboole_0(X2)|~v1_relat_1(X2)|~m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.47  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.47  cnf(c_0_33, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.47  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|~v1_xboole_0(k2_zfmisc_1(X4,X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.47  cnf(c_0_35, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.20/0.47  fof(c_0_36, plain, ![X50, X52, X53, X54, X55]:((r2_hidden(esk3_1(X50),X50)|X50=k1_xboole_0)&((~r2_hidden(X52,X50)|esk3_1(X50)!=k4_mcart_1(X52,X53,X54,X55)|X50=k1_xboole_0)&(~r2_hidden(X53,X50)|esk3_1(X50)!=k4_mcart_1(X52,X53,X54,X55)|X50=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.20/0.47  cnf(c_0_37, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0|~r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.47  cnf(c_0_38, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_39, plain, (k1_xboole_0=o_0_0_xboole_0), inference(split_conjunct,[status(thm)],[d2_xboole_0])).
% 0.20/0.47  cnf(c_0_40, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  cnf(c_0_41, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0|~r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk5_0)|~r2_hidden(X3,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_30])).
% 0.20/0.47  cnf(c_0_42, plain, (X1=o_0_0_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.47  cnf(c_0_43, negated_conjecture, (esk6_0!=o_0_0_xboole_0), inference(rw,[status(thm)],[c_0_40, c_0_39])).
% 0.20/0.47  cnf(c_0_44, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  cnf(c_0_45, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0|~r2_hidden(X1,esk5_0)|~r2_hidden(X2,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.20/0.47  cnf(c_0_46, negated_conjecture, (esk5_0!=o_0_0_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_39])).
% 0.20/0.47  cnf(c_0_47, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_49, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_42]), c_0_46])).
% 0.20/0.47  cnf(c_0_50, negated_conjecture, (esk4_0!=o_0_0_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_39])).
% 0.20/0.47  cnf(c_0_51, plain, (r2_hidden(X1,X2)|v1_xboole_0(k2_zfmisc_1(X2,X3))|~m1_subset_1(k4_tarski(X1,X4),k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_25])).
% 0.20/0.47  cnf(c_0_52, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_42]), c_0_50])).
% 0.20/0.47  cnf(c_0_53, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),X1)|v1_xboole_0(k2_zfmisc_1(X1,X2))|~m1_subset_1(esk8_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.47  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_53, c_0_32])).
% 0.20/0.47  fof(c_0_55, plain, ![X13, X14, X15, X16, X17]:((~r1_tarski(X13,X14)|(~r2_hidden(X15,X13)|r2_hidden(X15,X14)))&((r2_hidden(esk2_2(X16,X17),X16)|r1_tarski(X16,X17))&(~r2_hidden(esk2_2(X16,X17),X17)|r1_tarski(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.47  cnf(c_0_56, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_54])).
% 0.20/0.47  cnf(c_0_57, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.47  fof(c_0_58, plain, ![X29, X30]:(~r2_hidden(X29,X30)|~r1_tarski(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.47  cnf(c_0_59, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),X1)|r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.47  cnf(c_0_60, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.47  cnf(c_0_61, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),X1)|r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_42]), c_0_43])).
% 0.20/0.47  cnf(c_0_62, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.47  cnf(c_0_63, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  fof(c_0_64, plain, ![X56, X57, X58, X59]:(((k5_mcart_1(X56,X57,X58,X59)=k1_mcart_1(k1_mcart_1(X59))|~m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))|(X56=k1_xboole_0|X57=k1_xboole_0|X58=k1_xboole_0))&(k6_mcart_1(X56,X57,X58,X59)=k2_mcart_1(k1_mcart_1(X59))|~m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))|(X56=k1_xboole_0|X57=k1_xboole_0|X58=k1_xboole_0)))&(k7_mcart_1(X56,X57,X58,X59)=k2_mcart_1(X59)|~m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))|(X56=k1_xboole_0|X57=k1_xboole_0|X58=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.20/0.47  cnf(c_0_65, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,esk5_0)|~r2_hidden(X2,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_30])).
% 0.20/0.47  fof(c_0_66, plain, ![X45, X46, X47]:((r2_hidden(k1_mcart_1(X45),X46)|~r2_hidden(X45,k2_zfmisc_1(X46,X47)))&(r2_hidden(k2_mcart_1(X45),X47)|~r2_hidden(X45,k2_zfmisc_1(X46,X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.20/0.47  cnf(c_0_67, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))|v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_63])).
% 0.20/0.47  fof(c_0_68, plain, ![X37, X38, X39, X40]:(~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|m1_subset_1(k5_mcart_1(X37,X38,X39,X40),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).
% 0.20/0.47  cnf(c_0_69, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.47  cnf(c_0_70, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_42]), c_0_46])).
% 0.20/0.47  fof(c_0_71, plain, ![X23, X24]:(~r2_hidden(X23,X24)|m1_subset_1(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.47  cnf(c_0_72, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.47  cnf(c_0_73, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))|v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_42]), c_0_43])).
% 0.20/0.47  cnf(c_0_74, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.47  cnf(c_0_75, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_69, c_0_27])).
% 0.20/0.47  fof(c_0_76, plain, ![X41, X42, X43, X44]:(~m1_subset_1(X44,k3_zfmisc_1(X41,X42,X43))|m1_subset_1(k7_mcart_1(X41,X42,X43,X44),X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 0.20/0.47  cnf(c_0_77, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.47  fof(c_0_78, plain, ![X31, X32, X33]:k3_mcart_1(X31,X32,X33)=k4_tarski(k4_tarski(X31,X32),X33), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.47  cnf(c_0_79, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_42]), c_0_50])).
% 0.20/0.47  cnf(c_0_80, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.47  cnf(c_0_81, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk8_0)),esk5_0)|v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.47  cnf(c_0_82, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_74, c_0_27])).
% 0.20/0.47  cnf(c_0_83, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=o_0_0_xboole_0|X2=o_0_0_xboole_0|X3=o_0_0_xboole_0|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_39]), c_0_39]), c_0_39])).
% 0.20/0.47  cnf(c_0_84, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.47  cnf(c_0_85, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_77, c_0_27])).
% 0.20/0.47  cnf(c_0_86, negated_conjecture, (esk7_0=X1|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  cnf(c_0_87, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.47  cnf(c_0_88, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk8_0)),k2_mcart_1(k1_mcart_1(esk8_0)))=k1_mcart_1(esk8_0)|v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_73]), c_0_33])])).
% 0.20/0.47  cnf(c_0_89, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_79])).
% 0.20/0.47  cnf(c_0_90, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk8_0)),esk5_0)|v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.47  cnf(c_0_91, plain, (X1=o_0_0_xboole_0|X2=o_0_0_xboole_0|X3=o_0_0_xboole_0|m1_subset_1(k1_mcart_1(k1_mcart_1(X4)),X1)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.47  cnf(c_0_92, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_84, c_0_27])).
% 0.20/0.47  cnf(c_0_93, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=o_0_0_xboole_0|X2=o_0_0_xboole_0|X3=o_0_0_xboole_0|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_39]), c_0_39]), c_0_39])).
% 0.20/0.47  cnf(c_0_94, negated_conjecture, (esk7_0=X1|esk8_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.47  cnf(c_0_95, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk8_0)),k2_mcart_1(k1_mcart_1(esk8_0)))=k1_mcart_1(esk8_0)), inference(sr,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.47  cnf(c_0_96, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk8_0)),esk5_0)), inference(sr,[status(thm)],[c_0_90, c_0_89])).
% 0.20/0.47  cnf(c_0_97, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk8_0)),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_32]), c_0_50]), c_0_46]), c_0_43])).
% 0.20/0.47  cnf(c_0_98, plain, (X1=o_0_0_xboole_0|X2=o_0_0_xboole_0|X3=o_0_0_xboole_0|m1_subset_1(k2_mcart_1(X4),X3)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.47  cnf(c_0_99, negated_conjecture, (esk7_0=k1_mcart_1(k1_mcart_1(esk8_0))|k4_tarski(k1_mcart_1(esk8_0),X1)!=esk8_0|~m1_subset_1(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_97])])).
% 0.20/0.47  cnf(c_0_100, negated_conjecture, (m1_subset_1(k2_mcart_1(esk8_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_32]), c_0_50]), c_0_46]), c_0_43])).
% 0.20/0.47  cnf(c_0_101, negated_conjecture, (esk7_0!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  cnf(c_0_102, negated_conjecture, (esk7_0=k1_mcart_1(k1_mcart_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_52])])).
% 0.20/0.47  cnf(c_0_103, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)!=k1_mcart_1(k1_mcart_1(esk8_0))), inference(rw,[status(thm)],[c_0_101, c_0_102])).
% 0.20/0.47  cnf(c_0_104, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_83]), c_0_32])]), c_0_43]), c_0_46]), c_0_50]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 105
% 0.20/0.47  # Proof object clause steps            : 71
% 0.20/0.47  # Proof object formula steps           : 34
% 0.20/0.47  # Proof object conjectures             : 43
% 0.20/0.47  # Proof object clause conjectures      : 40
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 25
% 0.20/0.47  # Proof object initial formulas used   : 17
% 0.20/0.47  # Proof object generating inferences   : 31
% 0.20/0.47  # Proof object simplifying inferences  : 46
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 17
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 32
% 0.20/0.47  # Removed in clause preprocessing      : 2
% 0.20/0.47  # Initial clauses in saturation        : 30
% 0.20/0.47  # Processed clauses                    : 1258
% 0.20/0.47  # ...of these trivial                  : 3
% 0.20/0.47  # ...subsumed                          : 915
% 0.20/0.47  # ...remaining for further processing  : 340
% 0.20/0.47  # Other redundant clauses eliminated   : 0
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 70
% 0.20/0.47  # Backward-rewritten                   : 40
% 0.20/0.47  # Generated clauses                    : 4017
% 0.20/0.47  # ...of the previous two non-trivial   : 3954
% 0.20/0.47  # Contextual simplify-reflections      : 4
% 0.20/0.47  # Paramodulations                      : 4014
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 0
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 197
% 0.20/0.47  #    Positive orientable unit clauses  : 14
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 8
% 0.20/0.47  #    Non-unit-clauses                  : 175
% 0.20/0.47  # Current number of unprocessed clauses: 2592
% 0.20/0.47  # ...number of literals in the above   : 9125
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 145
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 13663
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 10777
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 904
% 0.20/0.47  # Unit Clause-clause subsumption calls : 241
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 15
% 0.20/0.47  # BW rewrite match successes           : 11
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 57634
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.117 s
% 0.20/0.47  # System time              : 0.007 s
% 0.20/0.47  # Total time               : 0.125 s
% 0.20/0.47  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
