%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t104_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:47 EDT 2019

% Result     : Theorem 233.14s
% Output     : CNFRefutation 233.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  82 expanded)
%              Number of clauses        :   27 (  36 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  164 ( 338 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t104_relat_1.p',t104_relat_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t104_relat_1.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t104_relat_1.p',dt_k7_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t104_relat_1.p',t3_subset)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t104_relat_1.p',d3_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t104_relat_1.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t104_relat_1.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t104_relat_1.p',t2_subset)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t104_relat_1])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X14,X12)
        | ~ r2_hidden(k4_tarski(X14,X15),X13)
        | X13 != k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X14,X15),X11)
        | ~ r2_hidden(k4_tarski(X14,X15),X13)
        | X13 != k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X16,X12)
        | ~ r2_hidden(k4_tarski(X16,X17),X11)
        | r2_hidden(k4_tarski(X16,X17),X13)
        | X13 != k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X13)
        | ~ r2_hidden(esk4_3(X11,X12,X13),X12)
        | ~ r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X11)
        | X13 = k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk4_3(X11,X12,X13),X12)
        | r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X13)
        | X13 = k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X11)
        | r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X13)
        | X13 = k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | v1_relat_1(k7_relat_1(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_11,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X35,k1_zfmisc_1(X36))
        | r1_tarski(X35,X36) )
      & ( ~ r1_tarski(X35,X36)
        | m1_subset_1(X35,k1_zfmisc_1(X36)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k7_relat_1(esk3_0,esk1_0),k7_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r1_tarski(X20,X21)
        | ~ r2_hidden(k4_tarski(X22,X23),X20)
        | r2_hidden(k4_tarski(X22,X23),X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk6_2(X20,X24),esk7_2(X20,X24)),X20)
        | r1_tarski(X20,X24)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk6_2(X20,X24),esk7_2(X20,X24)),X24)
        | r1_tarski(X20,X24)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k7_relat_1(X3,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X39))
      | m1_subset_1(X37,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk6_2(X1,X2),esk7_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk6_2(X1,X2),esk7_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X33,X34)
      | v1_xboole_0(X34)
      | r2_hidden(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k7_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk6_2(X1,k7_relat_1(X2,X3)),esk7_2(X1,k7_relat_1(X2,X3))),X2)
    | ~ r2_hidden(esk6_2(X1,k7_relat_1(X2,X3)),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk6_2(k7_relat_1(X1,X2),X3),esk7_2(k7_relat_1(X1,X2),X3)),X1)
    | r1_tarski(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_15])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ r2_hidden(esk6_2(k7_relat_1(X1,X2),k7_relat_1(X1,X3)),X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k7_relat_1(X4,X2))
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X1,esk2_0))
    | ~ r2_hidden(esk6_2(k7_relat_1(X1,X2),k7_relat_1(X1,esk2_0)),esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( r2_hidden(esk6_2(k7_relat_1(X1,X2),X3),X2)
    | r1_tarski(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_24]),c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk3_0,esk1_0),k7_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k7_relat_1(X1,esk1_0),k7_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
