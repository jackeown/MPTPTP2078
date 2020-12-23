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
% DateTime   : Thu Dec  3 10:58:16 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 128 expanded)
%              Number of clauses        :   30 (  53 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  181 ( 504 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ! [X4] :
                  ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                <=> ? [X5] :
                      ( m1_subset_1(X5,X2)
                      & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ! [X4] :
                    ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,X2)
                        & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_relset_1])).

fof(c_0_13,plain,(
    ! [X42,X43,X44] :
      ( ( v4_relat_1(X44,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( v5_relat_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_14,negated_conjecture,(
    ! [X52] :
      ( ~ v1_xboole_0(esk6_0)
      & ~ v1_xboole_0(esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk6_0)))
      & ( ~ r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))
        | ~ m1_subset_1(X52,esk7_0)
        | ~ r2_hidden(k4_tarski(X52,esk9_0),esk8_0) )
      & ( m1_subset_1(esk10_0,esk7_0)
        | r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0)) )
      & ( r2_hidden(k4_tarski(esk10_0,esk9_0),esk8_0)
        | r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_15,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | v1_relat_1(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,plain,(
    ! [X34,X35] : v1_relat_1(k2_zfmisc_1(X34,X35)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_17,plain,(
    ! [X21,X22] :
      ( ( ~ v4_relat_1(X22,X21)
        | r1_tarski(k1_relat_1(X22),X21)
        | ~ v1_relat_1(X22) )
      & ( ~ r1_tarski(k1_relat_1(X22),X21)
        | v4_relat_1(X22,X21)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_18,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v4_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_21])])).

fof(c_0_27,plain,(
    ! [X36,X37,X38,X40] :
      ( ( r2_hidden(esk5_3(X36,X37,X38),k1_relat_1(X38))
        | ~ r2_hidden(X36,k9_relat_1(X38,X37))
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(k4_tarski(esk5_3(X36,X37,X38),X36),X38)
        | ~ r2_hidden(X36,k9_relat_1(X38,X37))
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(esk5_3(X36,X37,X38),X37)
        | ~ r2_hidden(X36,k9_relat_1(X38,X37))
        | ~ v1_relat_1(X38) )
      & ( ~ r2_hidden(X40,k1_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X40,X36),X38)
        | ~ r2_hidden(X40,X37)
        | r2_hidden(X36,k9_relat_1(X38,X37))
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_31,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( ~ r2_hidden(X25,X24)
        | r2_hidden(k4_tarski(esk2_3(X23,X24,X25),X25),X23)
        | X24 != k2_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X28,X27),X23)
        | r2_hidden(X27,X24)
        | X24 != k2_relat_1(X23) )
      & ( ~ r2_hidden(esk3_2(X29,X30),X30)
        | ~ r2_hidden(k4_tarski(X32,esk3_2(X29,X30)),X29)
        | X30 = k2_relat_1(X29) )
      & ( r2_hidden(esk3_2(X29,X30),X30)
        | r2_hidden(k4_tarski(esk4_2(X29,X30),esk3_2(X29,X30)),X29)
        | X30 = k2_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))
    | ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(X1,esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | m1_subset_1(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk8_0),esk7_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk9_0),esk8_0)
    | r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(esk5_3(esk9_0,X1,esk8_0),esk7_0)
    | ~ r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))
    | r2_hidden(esk9_0,X1)
    | X1 != k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_44,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k2_relset_1(X45,X46,X47) = k2_relat_1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))
    | ~ r2_hidden(esk5_3(esk9_0,X1,esk8_0),esk7_0)
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_26])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))
    | r2_hidden(esk9_0,k2_relat_1(esk8_0)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_19])])).

fof(c_0_51,plain,(
    ! [X41] :
      ( ~ v1_relat_1(X41)
      | k9_relat_1(X41,k1_relat_1(X41)) = k2_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_50]),c_0_19])])).

cnf(c_0_53,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_50]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:43:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.12/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.033 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t48_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 0.12/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.12/0.38  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.12/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.38  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.12/0.38  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.12/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.12/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.38  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.12/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3))))))), inference(assume_negation,[status(cth)],[t48_relset_1])).
% 0.12/0.38  fof(c_0_13, plain, ![X42, X43, X44]:((v4_relat_1(X44,X42)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(v5_relat_1(X44,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.38  fof(c_0_14, negated_conjecture, ![X52]:(~v1_xboole_0(esk6_0)&(~v1_xboole_0(esk7_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk6_0)))&((~r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))|(~m1_subset_1(X52,esk7_0)|~r2_hidden(k4_tarski(X52,esk9_0),esk8_0)))&((m1_subset_1(esk10_0,esk7_0)|r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0)))&(r2_hidden(k4_tarski(esk10_0,esk9_0),esk8_0)|r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.12/0.38  fof(c_0_15, plain, ![X19, X20]:(~v1_relat_1(X19)|(~m1_subset_1(X20,k1_zfmisc_1(X19))|v1_relat_1(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.38  fof(c_0_16, plain, ![X34, X35]:v1_relat_1(k2_zfmisc_1(X34,X35)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.38  fof(c_0_17, plain, ![X21, X22]:((~v4_relat_1(X22,X21)|r1_tarski(k1_relat_1(X22),X21)|~v1_relat_1(X22))&(~r1_tarski(k1_relat_1(X22),X21)|v4_relat_1(X22,X21)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.12/0.38  cnf(c_0_18, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_20, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_21, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  fof(c_0_22, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.12/0.38  fof(c_0_23, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.38  cnf(c_0_24, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (v4_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_19]), c_0_21])])).
% 0.12/0.38  fof(c_0_27, plain, ![X36, X37, X38, X40]:((((r2_hidden(esk5_3(X36,X37,X38),k1_relat_1(X38))|~r2_hidden(X36,k9_relat_1(X38,X37))|~v1_relat_1(X38))&(r2_hidden(k4_tarski(esk5_3(X36,X37,X38),X36),X38)|~r2_hidden(X36,k9_relat_1(X38,X37))|~v1_relat_1(X38)))&(r2_hidden(esk5_3(X36,X37,X38),X37)|~r2_hidden(X36,k9_relat_1(X38,X37))|~v1_relat_1(X38)))&(~r2_hidden(X40,k1_relat_1(X38))|~r2_hidden(k4_tarski(X40,X36),X38)|~r2_hidden(X40,X37)|r2_hidden(X36,k9_relat_1(X38,X37))|~v1_relat_1(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.12/0.38  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.12/0.38  fof(c_0_31, plain, ![X23, X24, X25, X27, X28, X29, X30, X32]:(((~r2_hidden(X25,X24)|r2_hidden(k4_tarski(esk2_3(X23,X24,X25),X25),X23)|X24!=k2_relat_1(X23))&(~r2_hidden(k4_tarski(X28,X27),X23)|r2_hidden(X27,X24)|X24!=k2_relat_1(X23)))&((~r2_hidden(esk3_2(X29,X30),X30)|~r2_hidden(k4_tarski(X32,esk3_2(X29,X30)),X29)|X30=k2_relat_1(X29))&(r2_hidden(esk3_2(X29,X30),X30)|r2_hidden(k4_tarski(esk4_2(X29,X30),esk3_2(X29,X30)),X29)|X30=k2_relat_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))|~m1_subset_1(X1,esk7_0)|~r2_hidden(k4_tarski(X1,esk9_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  fof(c_0_34, plain, ![X17, X18]:(~r2_hidden(X17,X18)|m1_subset_1(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.12/0.38  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (k3_xboole_0(k1_relat_1(esk8_0),esk7_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.38  cnf(c_0_37, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk9_0),esk8_0)|r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (~m1_subset_1(esk5_3(esk9_0,X1,esk8_0),esk7_0)|~r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26])])).
% 0.12/0.38  cnf(c_0_40, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.38  cnf(c_0_42, plain, (r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))|r2_hidden(esk9_0,X1)|X1!=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.38  fof(c_0_44, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k2_relset_1(X45,X46,X47)=k2_relat_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))|~r2_hidden(esk5_3(esk9_0,X1,esk8_0),esk7_0)|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_26])])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))|r2_hidden(esk9_0,k2_relat_1(esk8_0))), inference(er,[status(thm)],[c_0_43])).
% 0.12/0.38  cnf(c_0_48, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk9_0,k2_relset_1(esk7_0,esk6_0,esk8_0))|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_19])])).
% 0.12/0.38  fof(c_0_51, plain, ![X41]:(~v1_relat_1(X41)|k9_relat_1(X41,k1_relat_1(X41))=k2_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_48]), c_0_50]), c_0_19])])).
% 0.12/0.38  cnf(c_0_53, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_50]), c_0_26])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 55
% 0.12/0.38  # Proof object clause steps            : 30
% 0.12/0.38  # Proof object formula steps           : 25
% 0.12/0.38  # Proof object conjectures             : 20
% 0.12/0.38  # Proof object clause conjectures      : 17
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 15
% 0.12/0.38  # Proof object initial formulas used   : 12
% 0.12/0.38  # Proof object generating inferences   : 15
% 0.12/0.38  # Proof object simplifying inferences  : 16
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 12
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 30
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 30
% 0.12/0.38  # Processed clauses                    : 91
% 0.12/0.38  # ...of these trivial                  : 4
% 0.12/0.38  # ...subsumed                          : 1
% 0.12/0.38  # ...remaining for further processing  : 86
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 3
% 0.12/0.38  # Backward-rewritten                   : 2
% 0.12/0.38  # Generated clauses                    : 106
% 0.12/0.38  # ...of the previous two non-trivial   : 100
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 97
% 0.12/0.38  # Factorizations                       : 4
% 0.12/0.38  # Equation resolutions                 : 5
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 51
% 0.12/0.38  #    Positive orientable unit clauses  : 8
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 4
% 0.12/0.38  #    Non-unit-clauses                  : 39
% 0.12/0.38  # Current number of unprocessed clauses: 68
% 0.12/0.38  # ...number of literals in the above   : 237
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 35
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 343
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 196
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.12/0.38  # Unit Clause-clause subsumption calls : 24
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 3972
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.042 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.046 s
% 0.12/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
