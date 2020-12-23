%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t49_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:08 EDT 2019

% Result     : Theorem 224.40s
% Output     : CNFRefutation 224.40s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 254 expanded)
%              Number of clauses        :   44 ( 117 expanded)
%              Number of leaves         :   13 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  210 ( 695 expanded)
%              Number of equality atoms :   97 ( 446 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
          & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
          & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t49_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',d3_zfmisc_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t48_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',dt_k6_mcart_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t3_subset)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t29_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t4_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t6_boole)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t135_zfmisc_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',dt_k5_mcart_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t35_mcart_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t3_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
            & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
            & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t49_mcart_1])).

fof(c_0_14,negated_conjecture,
    ( ( r1_tarski(esk1_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
      | r1_tarski(esk1_0,k3_zfmisc_1(esk2_0,esk3_0,esk1_0))
      | r1_tarski(esk1_0,k3_zfmisc_1(esk3_0,esk1_0,esk2_0)) )
    & esk1_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] : k3_zfmisc_1(X11,X12,X13) = k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X45,X46,X47,X48] :
      ( X45 = k1_xboole_0
      | X46 = k1_xboole_0
      | X47 = k1_xboole_0
      | ~ m1_subset_1(X48,k3_zfmisc_1(X45,X46,X47))
      | X48 = k3_mcart_1(k5_mcart_1(X45,X46,X47,X48),k6_mcart_1(X45,X46,X47,X48),k7_mcart_1(X45,X46,X47,X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ m1_subset_1(X21,k3_zfmisc_1(X18,X19,X20))
      | m1_subset_1(k6_mcart_1(X18,X19,X20,X21),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

fof(c_0_18,plain,(
    ! [X42,X43] :
      ( ( ~ m1_subset_1(X42,k1_zfmisc_1(X43))
        | r1_tarski(X42,X43) )
      & ( ~ r1_tarski(X42,X43)
        | m1_subset_1(X42,k1_zfmisc_1(X43)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(esk2_0,esk3_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(esk3_0,esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X32,X34,X35,X36] :
      ( ( r2_hidden(esk5_1(X32),X32)
        | X32 = k1_xboole_0 )
      & ( ~ r2_hidden(X34,X32)
        | esk5_1(X32) != k3_mcart_1(X34,X35,X36)
        | X32 = k1_xboole_0 )
      & ( ~ r2_hidden(X35,X32)
        | esk5_1(X32) != k3_mcart_1(X34,X35,X36)
        | X32 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X37,X38)
      | v1_xboole_0(X38)
      | r2_hidden(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_24,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | m1_subset_1(X49,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk1_0))
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_28,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk5_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_20])).

fof(c_0_32,plain,(
    ! [X55] :
      ( ~ v1_xboole_0(X55)
      | X55 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0),esk2_0)))
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk1_0))
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(esk5_1(X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | ~ r2_hidden(k6_mcart_1(X1,X2,X3,esk5_1(X4)),X4) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(k6_mcart_1(X2,X1,X3,X4),X1)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0),esk2_0))
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk1_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_41,plain,(
    ! [X28,X29] :
      ( ( ~ r1_tarski(X28,k2_zfmisc_1(X28,X29))
        | X28 = k1_xboole_0 )
      & ( ~ r1_tarski(X28,k2_zfmisc_1(X29,X28))
        | X28 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(esk5_1(X2),k2_zfmisc_1(k2_zfmisc_1(X3,X2),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_1(esk1_0),k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0),esk2_0))
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk1_0))
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

fof(c_0_44,plain,(
    ! [X14,X15,X16,X17] :
      ( ~ m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))
      | m1_subset_1(k5_mcart_1(X14,X15,X16,X17),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_40])).

cnf(c_0_47,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_40])).

fof(c_0_49,plain,(
    ! [X39,X40,X41] :
      ( ( X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | k3_zfmisc_1(X39,X40,X41) != k1_xboole_0 )
      & ( X39 != k1_xboole_0
        | k3_zfmisc_1(X39,X40,X41) = k1_xboole_0 )
      & ( X40 != k1_xboole_0
        | k3_zfmisc_1(X39,X40,X41) = k1_xboole_0 )
      & ( X41 != k1_xboole_0
        | k3_zfmisc_1(X39,X40,X41) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_50,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk5_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_48])).

cnf(c_0_53,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(esk5_1(X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | ~ r2_hidden(k5_mcart_1(X1,X2,X3,esk5_1(X4)),X4) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_29])])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(k5_mcart_1(X1,X2,X3,X4),X1)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_52])).

cnf(c_0_57,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_20])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(esk5_1(X3),k2_zfmisc_1(k2_zfmisc_1(X3,X2),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | m1_subset_1(esk5_1(esk1_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_39]),c_0_40])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_20])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_40])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_62])).

fof(c_0_66,plain,(
    ! [X44] :
      ( ~ r1_tarski(X44,k1_xboole_0)
      | X44 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_63]),c_0_64]),c_0_62]),c_0_65]),c_0_65])])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_67]),c_0_62]),c_0_65]),c_0_65]),c_0_64])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
