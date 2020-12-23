%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1082+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:42 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   25 (  34 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   84 ( 136 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d13_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ( m1_funct_2(X3,X1,X2)
      <=> ! [X4] :
            ( m1_subset_1(X4,X3)
           => ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

fof(t121_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t199_funct_2,conjecture,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => m1_funct_2(k1_funct_2(X1,X2),X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_funct_2)).

fof(fc1_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ v1_xboole_0(k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_funct_2)).

fof(c_0_5,plain,(
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

fof(c_0_6,plain,(
    ! [X12,X13,X14] :
      ( ( v1_funct_1(X14)
        | ~ r2_hidden(X14,k1_funct_2(X12,X13)) )
      & ( v1_funct_2(X14,X12,X13)
        | ~ r2_hidden(X14,k1_funct_2(X12,X13)) )
      & ( m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ r2_hidden(X14,k1_funct_2(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).

cnf(c_0_7,plain,
    ( m1_funct_2(X3,X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(esk1_3(X1,X2,X3))
    | ~ v1_funct_2(esk1_3(X1,X2,X3),X1,X2)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,X16)
      | v1_xboole_0(X16)
      | r2_hidden(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
       => m1_funct_2(k1_funct_2(X1,X2),X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t199_funct_2])).

cnf(c_0_13,plain,
    ( m1_funct_2(X1,X2,X3)
    | v1_xboole_0(X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),k1_funct_2(X2,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ~ m1_funct_2(k1_funct_2(esk2_0,esk3_0),esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_16,plain,
    ( m1_funct_2(X1,X2,X3)
    | v1_xboole_0(k1_funct_2(X2,X3))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(esk1_3(X2,X3,X1),k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X3)
    | m1_funct_2(X3,X1,X2)
    | v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( v1_xboole_0(X11)
      | ~ v1_xboole_0(k1_funct_2(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_funct_2])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ m1_funct_2(k1_funct_2(esk2_0,esk3_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( m1_funct_2(k1_funct_2(X1,X2),X1,X2)
    | v1_xboole_0(k1_funct_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_funct_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_xboole_0(k1_funct_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------
