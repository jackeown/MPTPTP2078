%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:55 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 126 expanded)
%              Number of clauses        :   22 (  44 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  244 ( 892 expanded)
%              Number of equality atoms :   70 ( 233 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
       => ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t54_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( X2 = k2_funct_1(X1)
            <=> ( k1_relat_1(X2) = k2_relat_1(X1)
                & ! [X3,X4] :
                    ( ( ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) )
                     => ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) ) )
                    & ( ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) )
                     => ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
         => ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t85_funct_2])).

fof(c_0_8,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_relset_1(X20,X21,X22) = k1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk5_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))
    & v2_funct_1(esk6_0)
    & r2_hidden(esk7_0,esk5_0)
    & r2_hidden(esk8_0,esk5_0)
    & k1_funct_1(esk6_0,esk7_0) = k1_funct_1(esk6_0,esk8_0)
    & esk7_0 != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( k1_relat_1(X11) = k2_relat_1(X10)
        | X11 != k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(X13,k1_relat_1(X10))
        | ~ r2_hidden(X12,k2_relat_1(X10))
        | X13 != k1_funct_1(X11,X12)
        | X11 != k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X12 = k1_funct_1(X10,X13)
        | ~ r2_hidden(X12,k2_relat_1(X10))
        | X13 != k1_funct_1(X11,X12)
        | X11 != k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(X14,k2_relat_1(X10))
        | ~ r2_hidden(X15,k1_relat_1(X10))
        | X14 != k1_funct_1(X10,X15)
        | X11 != k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X15 = k1_funct_1(X11,X14)
        | ~ r2_hidden(X15,k1_relat_1(X10))
        | X14 != k1_funct_1(X10,X15)
        | X11 != k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk4_2(X10,X11),k1_relat_1(X10))
        | r2_hidden(esk1_2(X10,X11),k2_relat_1(X10))
        | k1_relat_1(X11) != k2_relat_1(X10)
        | X11 = k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk3_2(X10,X11) = k1_funct_1(X10,esk4_2(X10,X11))
        | r2_hidden(esk1_2(X10,X11),k2_relat_1(X10))
        | k1_relat_1(X11) != k2_relat_1(X10)
        | X11 = k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk3_2(X10,X11),k2_relat_1(X10))
        | esk4_2(X10,X11) != k1_funct_1(X11,esk3_2(X10,X11))
        | r2_hidden(esk1_2(X10,X11),k2_relat_1(X10))
        | k1_relat_1(X11) != k2_relat_1(X10)
        | X11 = k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk4_2(X10,X11),k1_relat_1(X10))
        | esk2_2(X10,X11) = k1_funct_1(X11,esk1_2(X10,X11))
        | k1_relat_1(X11) != k2_relat_1(X10)
        | X11 = k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk3_2(X10,X11) = k1_funct_1(X10,esk4_2(X10,X11))
        | esk2_2(X10,X11) = k1_funct_1(X11,esk1_2(X10,X11))
        | k1_relat_1(X11) != k2_relat_1(X10)
        | X11 = k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk3_2(X10,X11),k2_relat_1(X10))
        | esk4_2(X10,X11) != k1_funct_1(X11,esk3_2(X10,X11))
        | esk2_2(X10,X11) = k1_funct_1(X11,esk1_2(X10,X11))
        | k1_relat_1(X11) != k2_relat_1(X10)
        | X11 = k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk4_2(X10,X11),k1_relat_1(X10))
        | ~ r2_hidden(esk2_2(X10,X11),k1_relat_1(X10))
        | esk1_2(X10,X11) != k1_funct_1(X10,esk2_2(X10,X11))
        | k1_relat_1(X11) != k2_relat_1(X10)
        | X11 = k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk3_2(X10,X11) = k1_funct_1(X10,esk4_2(X10,X11))
        | ~ r2_hidden(esk2_2(X10,X11),k1_relat_1(X10))
        | esk1_2(X10,X11) != k1_funct_1(X10,esk2_2(X10,X11))
        | k1_relat_1(X11) != k2_relat_1(X10)
        | X11 = k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk3_2(X10,X11),k2_relat_1(X10))
        | esk4_2(X10,X11) != k1_funct_1(X11,esk3_2(X10,X11))
        | ~ r2_hidden(esk2_2(X10,X11),k1_relat_1(X10))
        | esk1_2(X10,X11) != k1_funct_1(X10,esk2_2(X10,X11))
        | k1_relat_1(X11) != k2_relat_1(X10)
        | X11 = k2_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

fof(c_0_11,plain,(
    ! [X9] :
      ( ( v1_relat_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_funct_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_12,plain,(
    ! [X23,X24] :
      ( ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,X23,X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23)))
      | k1_relset_1(X23,X23,X24) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

cnf(c_0_13,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_relat_1(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,plain,(
    ! [X7,X8] : v1_relat_1(k2_zfmisc_1(X7,X8)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_17,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(X1,k1_relat_1(X4))
    | X3 != k1_funct_1(X4,X1)
    | X2 != k2_funct_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X4)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k1_relset_1(esk5_0,esk5_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk6_0,esk5_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2)) = X2
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])]),c_0_18]),c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_25])])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1)) = X1
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_23]),c_0_29])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk8_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk6_0,esk7_0) = k1_funct_1(esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk7_0)) = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( esk7_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_33]),c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.13/0.38  # and selection function SelectComplexG.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t85_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 0.13/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.38  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 0.13/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.13/0.38  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.13/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4)))), inference(assume_negation,[status(cth)],[t85_funct_2])).
% 0.13/0.38  fof(c_0_8, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k1_relset_1(X20,X21,X22)=k1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk5_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))))&(v2_funct_1(esk6_0)&(((r2_hidden(esk7_0,esk5_0)&r2_hidden(esk8_0,esk5_0))&k1_funct_1(esk6_0,esk7_0)=k1_funct_1(esk6_0,esk8_0))&esk7_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.38  fof(c_0_10, plain, ![X10, X11, X12, X13, X14, X15]:(((k1_relat_1(X11)=k2_relat_1(X10)|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(((r2_hidden(X13,k1_relat_1(X10))|(~r2_hidden(X12,k2_relat_1(X10))|X13!=k1_funct_1(X11,X12))|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(X12=k1_funct_1(X10,X13)|(~r2_hidden(X12,k2_relat_1(X10))|X13!=k1_funct_1(X11,X12))|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&((r2_hidden(X14,k2_relat_1(X10))|(~r2_hidden(X15,k1_relat_1(X10))|X14!=k1_funct_1(X10,X15))|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(X15=k1_funct_1(X11,X14)|(~r2_hidden(X15,k1_relat_1(X10))|X14!=k1_funct_1(X10,X15))|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))))&(((((r2_hidden(esk4_2(X10,X11),k1_relat_1(X10))|r2_hidden(esk1_2(X10,X11),k2_relat_1(X10))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(esk3_2(X10,X11)=k1_funct_1(X10,esk4_2(X10,X11))|r2_hidden(esk1_2(X10,X11),k2_relat_1(X10))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(~r2_hidden(esk3_2(X10,X11),k2_relat_1(X10))|esk4_2(X10,X11)!=k1_funct_1(X11,esk3_2(X10,X11))|r2_hidden(esk1_2(X10,X11),k2_relat_1(X10))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(((r2_hidden(esk4_2(X10,X11),k1_relat_1(X10))|esk2_2(X10,X11)=k1_funct_1(X11,esk1_2(X10,X11))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(esk3_2(X10,X11)=k1_funct_1(X10,esk4_2(X10,X11))|esk2_2(X10,X11)=k1_funct_1(X11,esk1_2(X10,X11))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(~r2_hidden(esk3_2(X10,X11),k2_relat_1(X10))|esk4_2(X10,X11)!=k1_funct_1(X11,esk3_2(X10,X11))|esk2_2(X10,X11)=k1_funct_1(X11,esk1_2(X10,X11))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))))&(((r2_hidden(esk4_2(X10,X11),k1_relat_1(X10))|(~r2_hidden(esk2_2(X10,X11),k1_relat_1(X10))|esk1_2(X10,X11)!=k1_funct_1(X10,esk2_2(X10,X11)))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(esk3_2(X10,X11)=k1_funct_1(X10,esk4_2(X10,X11))|(~r2_hidden(esk2_2(X10,X11),k1_relat_1(X10))|esk1_2(X10,X11)!=k1_funct_1(X10,esk2_2(X10,X11)))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(~r2_hidden(esk3_2(X10,X11),k2_relat_1(X10))|esk4_2(X10,X11)!=k1_funct_1(X11,esk3_2(X10,X11))|(~r2_hidden(esk2_2(X10,X11),k1_relat_1(X10))|esk1_2(X10,X11)!=k1_funct_1(X10,esk2_2(X10,X11)))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X9]:((v1_relat_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(v1_funct_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X23, X24]:(~v1_funct_1(X24)|~v1_funct_2(X24,X23,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23)))|k1_relset_1(X23,X23,X24)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.13/0.38  cnf(c_0_13, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  fof(c_0_15, plain, ![X5, X6]:(~v1_relat_1(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_relat_1(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X7, X8]:v1_relat_1(k2_zfmisc_1(X7,X8)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.38  cnf(c_0_17, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(X1,k1_relat_1(X4))|X3!=k1_funct_1(X4,X1)|X2!=k2_funct_1(X4)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X4)|~v1_relat_1(X4)|~v1_funct_1(X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_18, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_19, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_20, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (k1_relset_1(esk5_0,esk5_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk6_0,esk5_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_24, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2))=X2|~r2_hidden(X2,k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])]), c_0_18]), c_0_19])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (k1_relat_1(esk6_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_14]), c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_14]), c_0_25])])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1))=X1|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_23]), c_0_29])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk8_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k1_funct_1(esk6_0,esk7_0)=k1_funct_1(esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk7_0))=esk8_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (esk7_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_33]), c_0_34]), c_0_35]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 37
% 0.13/0.38  # Proof object clause steps            : 22
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 15
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 6
% 0.13/0.38  # Proof object simplifying inferences  : 17
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 7
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 28
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 79
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 77
% 0.13/0.38  # Other redundant clauses eliminated   : 9
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 1
% 0.13/0.38  # Generated clauses                    : 38
% 0.13/0.38  # ...of the previous two non-trivial   : 39
% 0.13/0.38  # Contextual simplify-reflections      : 10
% 0.13/0.38  # Paramodulations                      : 33
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 9
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
% 0.13/0.38  # Current number of processed clauses  : 43
% 0.13/0.38  #    Positive orientable unit clauses  : 22
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 20
% 0.13/0.38  # Current number of unprocessed clauses: 16
% 0.13/0.38  # ...number of literals in the above   : 87
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 29
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1009
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 24
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.13/0.38  # Unit Clause-clause subsumption calls : 7
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 7
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3884
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.008 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
