%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:57 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   36 (  64 expanded)
%              Number of clauses        :   21 (  23 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  278 ( 466 expanded)
%              Number of equality atoms :   88 ( 136 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X4)
          & r2_hidden(X3,X1) )
       => ( X2 = k1_xboole_0
          | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X4)
            & r2_hidden(X3,X1) )
         => ( X2 = k1_xboole_0
            | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_funct_2])).

fof(c_0_8,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_relset_1(X20,X21,X22) = k1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v2_funct_1(esk8_0)
    & r2_hidden(esk7_0,esk5_0)
    & esk6_0 != k1_xboole_0
    & k1_funct_1(k2_funct_1(esk8_0),k1_funct_1(esk8_0,esk7_0)) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_relat_1(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_11,plain,(
    ! [X7,X8] : v1_relat_1(k2_zfmisc_1(X7,X8)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_12,plain,(
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

fof(c_0_13,plain,(
    ! [X9] :
      ( ( v1_relat_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X9) )
      & ( v1_funct_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X9) )
      & ( v2_funct_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

fof(c_0_14,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_funct_2(X25,X23,X24)
        | X23 = k1_relset_1(X23,X24,X25)
        | X24 = k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_relset_1(X23,X24,X25)
        | v1_funct_2(X25,X23,X24)
        | X24 = k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( ~ v1_funct_2(X25,X23,X24)
        | X23 = k1_relset_1(X23,X24,X25)
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_relset_1(X23,X24,X25)
        | v1_funct_2(X25,X23,X24)
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( ~ v1_funct_2(X25,X23,X24)
        | X25 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X25 != k1_xboole_0
        | v1_funct_2(X25,X23,X24)
        | X23 = k1_xboole_0
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_15,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(X1,k1_relat_1(X4))
    | X3 != k1_funct_1(X4,X1)
    | X2 != k2_funct_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X4)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2)) = X2
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v2_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_16])]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk8_0),k1_funct_1(esk8_0,X1)) = X1
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk8_0),k1_funct_1(esk8_0,esk7_0)) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:00:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.14/0.39  # and selection function HSelectMinInfpos.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t32_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X4)&r2_hidden(X3,X1))=>(X2=k1_xboole_0|k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3))=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 0.14/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.39  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 0.14/0.39  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.14/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.14/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X4)&r2_hidden(X3,X1))=>(X2=k1_xboole_0|k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3))=X3)))), inference(assume_negation,[status(cth)],[t32_funct_2])).
% 0.14/0.39  fof(c_0_8, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k1_relset_1(X20,X21,X22)=k1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.39  fof(c_0_9, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((v2_funct_1(esk8_0)&r2_hidden(esk7_0,esk5_0))&(esk6_0!=k1_xboole_0&k1_funct_1(k2_funct_1(esk8_0),k1_funct_1(esk8_0,esk7_0))!=esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.14/0.39  fof(c_0_10, plain, ![X5, X6]:(~v1_relat_1(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_relat_1(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.39  fof(c_0_11, plain, ![X7, X8]:v1_relat_1(k2_zfmisc_1(X7,X8)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.39  fof(c_0_12, plain, ![X10, X11, X12, X13, X14, X15]:(((k1_relat_1(X11)=k2_relat_1(X10)|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(((r2_hidden(X13,k1_relat_1(X10))|(~r2_hidden(X12,k2_relat_1(X10))|X13!=k1_funct_1(X11,X12))|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(X12=k1_funct_1(X10,X13)|(~r2_hidden(X12,k2_relat_1(X10))|X13!=k1_funct_1(X11,X12))|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&((r2_hidden(X14,k2_relat_1(X10))|(~r2_hidden(X15,k1_relat_1(X10))|X14!=k1_funct_1(X10,X15))|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(X15=k1_funct_1(X11,X14)|(~r2_hidden(X15,k1_relat_1(X10))|X14!=k1_funct_1(X10,X15))|X11!=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))))&(((((r2_hidden(esk4_2(X10,X11),k1_relat_1(X10))|r2_hidden(esk1_2(X10,X11),k2_relat_1(X10))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(esk3_2(X10,X11)=k1_funct_1(X10,esk4_2(X10,X11))|r2_hidden(esk1_2(X10,X11),k2_relat_1(X10))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(~r2_hidden(esk3_2(X10,X11),k2_relat_1(X10))|esk4_2(X10,X11)!=k1_funct_1(X11,esk3_2(X10,X11))|r2_hidden(esk1_2(X10,X11),k2_relat_1(X10))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(((r2_hidden(esk4_2(X10,X11),k1_relat_1(X10))|esk2_2(X10,X11)=k1_funct_1(X11,esk1_2(X10,X11))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(esk3_2(X10,X11)=k1_funct_1(X10,esk4_2(X10,X11))|esk2_2(X10,X11)=k1_funct_1(X11,esk1_2(X10,X11))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(~r2_hidden(esk3_2(X10,X11),k2_relat_1(X10))|esk4_2(X10,X11)!=k1_funct_1(X11,esk3_2(X10,X11))|esk2_2(X10,X11)=k1_funct_1(X11,esk1_2(X10,X11))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))))&(((r2_hidden(esk4_2(X10,X11),k1_relat_1(X10))|(~r2_hidden(esk2_2(X10,X11),k1_relat_1(X10))|esk1_2(X10,X11)!=k1_funct_1(X10,esk2_2(X10,X11)))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(esk3_2(X10,X11)=k1_funct_1(X10,esk4_2(X10,X11))|(~r2_hidden(esk2_2(X10,X11),k1_relat_1(X10))|esk1_2(X10,X11)!=k1_funct_1(X10,esk2_2(X10,X11)))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(~r2_hidden(esk3_2(X10,X11),k2_relat_1(X10))|esk4_2(X10,X11)!=k1_funct_1(X11,esk3_2(X10,X11))|(~r2_hidden(esk2_2(X10,X11),k1_relat_1(X10))|esk1_2(X10,X11)!=k1_funct_1(X10,esk2_2(X10,X11)))|k1_relat_1(X11)!=k2_relat_1(X10)|X11=k2_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 0.14/0.39  fof(c_0_13, plain, ![X9]:(((v1_relat_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v2_funct_1(X9)))&(v1_funct_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v2_funct_1(X9))))&(v2_funct_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v2_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.14/0.39  fof(c_0_14, plain, ![X23, X24, X25]:((((~v1_funct_2(X25,X23,X24)|X23=k1_relset_1(X23,X24,X25)|X24=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X23!=k1_relset_1(X23,X24,X25)|v1_funct_2(X25,X23,X24)|X24=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&((~v1_funct_2(X25,X23,X24)|X23=k1_relset_1(X23,X24,X25)|X23!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X23!=k1_relset_1(X23,X24,X25)|v1_funct_2(X25,X23,X24)|X23!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))))&((~v1_funct_2(X25,X23,X24)|X25=k1_xboole_0|X23=k1_xboole_0|X24!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X25!=k1_xboole_0|v1_funct_2(X25,X23,X24)|X23=k1_xboole_0|X24!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.14/0.39  cnf(c_0_15, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_17, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_18, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_19, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(X1,k1_relat_1(X4))|X3!=k1_funct_1(X4,X1)|X2!=k2_funct_1(X4)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X4)|~v1_relat_1(X4)|~v1_funct_1(X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_20, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_21, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_22, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.39  cnf(c_0_27, plain, (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2))=X2|~r2_hidden(X2,k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])]), c_0_20]), c_0_21])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (v2_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_16])]), c_0_25])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_26, c_0_16])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (k1_funct_1(k2_funct_1(esk8_0),k1_funct_1(esk8_0,X1))=X1|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31])])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (k1_funct_1(k2_funct_1(esk8_0),k1_funct_1(esk8_0,esk7_0))!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 36
% 0.14/0.39  # Proof object clause steps            : 21
% 0.14/0.39  # Proof object formula steps           : 15
% 0.14/0.39  # Proof object conjectures             : 15
% 0.14/0.39  # Proof object clause conjectures      : 12
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 14
% 0.14/0.39  # Proof object initial formulas used   : 7
% 0.14/0.39  # Proof object generating inferences   : 6
% 0.14/0.39  # Proof object simplifying inferences  : 13
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 7
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 33
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 33
% 0.14/0.39  # Processed clauses                    : 96
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 2
% 0.14/0.39  # ...remaining for further processing  : 94
% 0.14/0.39  # Other redundant clauses eliminated   : 16
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 6
% 0.14/0.39  # Generated clauses                    : 68
% 0.14/0.39  # ...of the previous two non-trivial   : 65
% 0.14/0.39  # Contextual simplify-reflections      : 10
% 0.14/0.39  # Paramodulations                      : 49
% 0.14/0.39  # Factorizations                       : 8
% 0.14/0.39  # Equation resolutions                 : 16
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 46
% 0.14/0.39  #    Positive orientable unit clauses  : 15
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 2
% 0.14/0.39  #    Non-unit-clauses                  : 29
% 0.14/0.39  # Current number of unprocessed clauses: 35
% 0.14/0.39  # ...number of literals in the above   : 208
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 39
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1029
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 54
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 12
% 0.14/0.39  # Unit Clause-clause subsumption calls : 17
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 3
% 0.14/0.39  # BW rewrite match successes           : 3
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 5155
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.033 s
% 0.14/0.39  # System time              : 0.006 s
% 0.14/0.39  # Total time               : 0.039 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
