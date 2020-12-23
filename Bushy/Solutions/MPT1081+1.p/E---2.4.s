%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t198_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:40 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  39 expanded)
%              Number of clauses        :   14 (  15 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   94 ( 159 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t198_funct_2.p',t2_subset)).

fof(d13_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ( m1_funct_2(X3,X1,X2)
      <=> ! [X4] :
            ( m1_subset_1(X4,X3)
           => ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t198_funct_2.p',d13_funct_2)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t198_funct_2.p',d1_tarski)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t198_funct_2.p',fc2_xboole_0)).

fof(t198_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => m1_funct_2(k1_tarski(X3),X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t198_funct_2.p',t198_funct_2)).

fof(c_0_5,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X32,X33)
      | v1_xboole_0(X33)
      | r2_hidden(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13] :
      ( ( v1_funct_1(X13)
        | ~ m1_subset_1(X13,X12)
        | ~ m1_funct_2(X12,X10,X11)
        | v1_xboole_0(X12) )
      & ( v1_funct_2(X13,X10,X11)
        | ~ m1_subset_1(X13,X12)
        | ~ m1_funct_2(X12,X10,X11)
        | v1_xboole_0(X12) )
      & ( m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ m1_subset_1(X13,X12)
        | ~ m1_funct_2(X12,X10,X11)
        | v1_xboole_0(X12) )
      & ( m1_subset_1(esk4_3(X10,X11,X12),X12)
        | m1_funct_2(X12,X10,X11)
        | v1_xboole_0(X12) )
      & ( ~ v1_funct_1(esk4_3(X10,X11,X12))
        | ~ v1_funct_2(esk4_3(X10,X11,X12),X10,X11)
        | ~ m1_subset_1(esk4_3(X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | m1_funct_2(X12,X10,X11)
        | v1_xboole_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_funct_2])])])])])])).

fof(c_0_7,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X15
        | X16 != k1_tarski(X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_tarski(X15) )
      & ( ~ r2_hidden(esk5_2(X19,X20),X20)
        | esk5_2(X19,X20) != X19
        | X20 = k1_tarski(X19) )
      & ( r2_hidden(esk5_2(X19,X20),X20)
        | esk5_2(X19,X20) = X19
        | X20 = k1_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_8,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),X3)
    | m1_funct_2(X3,X1,X2)
    | v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk4_3(X2,X3,X1),X1)
    | m1_funct_2(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_12,plain,(
    ! [X47] : ~ v1_xboole_0(k1_tarski(X47)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_13,plain,
    ( esk4_3(X1,X2,X3) = X4
    | v1_xboole_0(X3)
    | m1_funct_2(X3,X1,X2)
    | X3 != k1_tarski(X4) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => m1_funct_2(k1_tarski(X3),X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t198_funct_2])).

cnf(c_0_16,plain,
    ( m1_funct_2(X3,X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(esk4_3(X1,X2,X3))
    | ~ v1_funct_2(esk4_3(X1,X2,X3),X1,X2)
    | ~ m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( esk4_3(X1,X2,k1_tarski(X3)) = X3
    | m1_funct_2(k1_tarski(X3),X1,X2) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ~ m1_funct_2(k1_tarski(esk3_0),esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( m1_funct_2(k1_tarski(X1),X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_funct_2(k1_tarski(esk3_0),esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
