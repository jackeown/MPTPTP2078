%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1081+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:42 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  39 expanded)
%              Number of clauses        :   14 (  15 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   92 ( 157 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d13_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ( m1_funct_2(X3,X1,X2)
      <=> ! [X4] :
            ( m1_subset_1(X4,X3)
           => ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t198_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => m1_funct_2(k1_tarski(X3),X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_funct_2)).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X18,X19)
      | v1_xboole_0(X19)
      | r2_hidden(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8] :
      ( ( v1_funct_1(X8)
        | ~ m1_subset_1(X8,X7)
        | ~ m1_funct_2(X7,X5,X6)
        | v1_xboole_0(X7) )
      & ( v1_funct_2(X8,X5,X6)
        | ~ m1_subset_1(X8,X7)
        | ~ m1_funct_2(X7,X5,X6)
        | v1_xboole_0(X7) )
      & ( m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ m1_subset_1(X8,X7)
        | ~ m1_funct_2(X7,X5,X6)
        | v1_xboole_0(X7) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),X7)
        | m1_funct_2(X7,X5,X6)
        | v1_xboole_0(X7) )
      & ( ~ v1_funct_1(esk1_3(X5,X6,X7))
        | ~ v1_funct_2(esk1_3(X5,X6,X7),X5,X6)
        | ~ m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | m1_funct_2(X7,X5,X6)
        | v1_xboole_0(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_funct_2])])])])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X3)
    | m1_funct_2(X3,X1,X2)
    | v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X17] : ~ v1_xboole_0(k1_tarski(X17)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | m1_funct_2(X3,X1,X2)
    | v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

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
    | ~ v1_funct_1(esk1_3(X1,X2,X3))
    | ~ v1_funct_2(esk1_3(X1,X2,X3),X1,X2)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( esk1_3(X1,X2,k1_tarski(X3)) = X3
    | m1_funct_2(k1_tarski(X3),X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & ~ m1_funct_2(k1_tarski(esk5_0),esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( m1_funct_2(k1_tarski(X1),X2,X3)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_funct_2(k1_tarski(esk5_0),esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------
