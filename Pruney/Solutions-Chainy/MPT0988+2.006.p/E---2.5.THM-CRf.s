%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   92 (15991 expanded)
%              Number of clauses        :   77 (5583 expanded)
%              Number of leaves         :    7 (3977 expanded)
%              Depth                    :   19
%              Number of atoms          :  499 (196693 expanded)
%              Number of equality atoms :  203 (81212 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & v2_funct_1(X3)
              & ! [X5,X6] :
                  ( ( ( r2_hidden(X5,X2)
                      & k1_funct_1(X4,X5) = X6 )
                   => ( r2_hidden(X6,X1)
                      & k1_funct_1(X3,X6) = X5 ) )
                  & ( ( r2_hidden(X6,X1)
                      & k1_funct_1(X3,X6) = X5 )
                   => ( r2_hidden(X5,X2)
                      & k1_funct_1(X4,X5) = X6 ) ) ) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( ( k2_relset_1(X1,X2,X3) = X2
                & v2_funct_1(X3)
                & ! [X5,X6] :
                    ( ( ( r2_hidden(X5,X2)
                        & k1_funct_1(X4,X5) = X6 )
                     => ( r2_hidden(X6,X1)
                        & k1_funct_1(X3,X6) = X5 ) )
                    & ( ( r2_hidden(X6,X1)
                        & k1_funct_1(X3,X6) = X5 )
                     => ( r2_hidden(X5,X2)
                        & k1_funct_1(X4,X5) = X6 ) ) ) )
             => ( X1 = k1_xboole_0
                | X2 = k1_xboole_0
                | X4 = k2_funct_1(X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_funct_2])).

fof(c_0_8,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k2_relset_1(X24,X25,X26) = k2_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X34,X35] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk5_0,esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk5_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))
      & k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0
      & v2_funct_1(esk7_0)
      & ( r2_hidden(X35,esk5_0)
        | ~ r2_hidden(X34,esk6_0)
        | k1_funct_1(esk8_0,X34) != X35 )
      & ( k1_funct_1(esk7_0,X35) = X34
        | ~ r2_hidden(X34,esk6_0)
        | k1_funct_1(esk8_0,X34) != X35 )
      & ( r2_hidden(X34,esk6_0)
        | ~ r2_hidden(X35,esk5_0)
        | k1_funct_1(esk7_0,X35) != X34 )
      & ( k1_funct_1(esk8_0,X34) = X35
        | ~ r2_hidden(X35,esk5_0)
        | k1_funct_1(esk7_0,X35) != X34 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk8_0 != k2_funct_1(esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_11,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_12,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_13,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( k1_relat_1(X12) = k2_relat_1(X11)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(X14,k1_relat_1(X11))
        | ~ r2_hidden(X13,k2_relat_1(X11))
        | X14 != k1_funct_1(X12,X13)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X13 = k1_funct_1(X11,X14)
        | ~ r2_hidden(X13,k2_relat_1(X11))
        | X14 != k1_funct_1(X12,X13)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(X15,k2_relat_1(X11))
        | ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X16 = k1_funct_1(X12,X15)
        | ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_2(X11,X12),k1_relat_1(X11))
        | r2_hidden(esk1_2(X11,X12),k2_relat_1(X11))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk3_2(X11,X12) = k1_funct_1(X11,esk4_2(X11,X12))
        | r2_hidden(esk1_2(X11,X12),k2_relat_1(X11))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk3_2(X11,X12),k2_relat_1(X11))
        | esk4_2(X11,X12) != k1_funct_1(X12,esk3_2(X11,X12))
        | r2_hidden(esk1_2(X11,X12),k2_relat_1(X11))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_2(X11,X12),k1_relat_1(X11))
        | esk2_2(X11,X12) = k1_funct_1(X12,esk1_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk3_2(X11,X12) = k1_funct_1(X11,esk4_2(X11,X12))
        | esk2_2(X11,X12) = k1_funct_1(X12,esk1_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk3_2(X11,X12),k2_relat_1(X11))
        | esk4_2(X11,X12) != k1_funct_1(X12,esk3_2(X11,X12))
        | esk2_2(X11,X12) = k1_funct_1(X12,esk1_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_2(X11,X12),k1_relat_1(X11))
        | ~ r2_hidden(esk2_2(X11,X12),k1_relat_1(X11))
        | esk1_2(X11,X12) != k1_funct_1(X11,esk2_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk3_2(X11,X12) = k1_funct_1(X11,esk4_2(X11,X12))
        | ~ r2_hidden(esk2_2(X11,X12),k1_relat_1(X11))
        | esk1_2(X11,X12) != k1_funct_1(X11,esk2_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk3_2(X11,X12),k2_relat_1(X11))
        | esk4_2(X11,X12) != k1_funct_1(X12,esk3_2(X11,X12))
        | ~ r2_hidden(esk2_2(X11,X12),k1_relat_1(X11))
        | esk1_2(X11,X12) != k1_funct_1(X11,esk2_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

cnf(c_0_14,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X29 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X29 != k1_xboole_0
        | v1_funct_2(X29,X27,X28)
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_20,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_18])])).

cnf(c_0_27,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k1_relset_1(esk6_0,esk5_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk6_0)
    | k1_funct_1(esk8_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,X1)) = esk3_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk1_2(esk7_0,X1),esk6_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_21]),c_0_18])])).

cnf(c_0_36,negated_conjecture,
    ( esk8_0 != k2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0)
    | r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,X1)) = esk3_2(esk7_0,X1)
    | k1_funct_1(X1,esk1_2(esk7_0,X1)) = esk2_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_23]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = X2
    | ~ r2_hidden(X2,esk6_0)
    | k1_funct_1(esk8_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | esk1_2(X1,X2) != k1_funct_1(X1,esk2_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0)
    | r2_hidden(k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk5_0)
    | k1_funct_1(esk7_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),esk5_0)
    | r2_hidden(esk1_2(esk7_0,X1),esk6_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_23]),c_0_24]),c_0_45]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk8_0,X1)) = X1
    | ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,X1)) = esk3_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,X1)) != esk1_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk2_2(esk7_0,X1),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_24]),c_0_23]),c_0_25]),c_0_26])])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0)
    | r2_hidden(esk2_2(esk7_0,esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)
    | r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))) = esk1_2(esk7_0,esk8_0)
    | k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0)) != esk1_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_59,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = X2
    | ~ r2_hidden(X2,esk5_0)
    | k1_funct_1(esk7_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X2,esk3_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)),esk6_0)
    | r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_49]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( k1_funct_1(X1,esk1_2(esk7_0,X1)) = esk2_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),esk5_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_23]),c_0_45]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk7_0,X1)) = X1
    | ~ r2_hidden(X1,esk5_0) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk1_2(esk7_0,X1),esk6_0)
    | k1_funct_1(X1,esk3_2(esk7_0,X1)) != esk4_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk3_2(esk7_0,X1),esk6_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_24]),c_0_23]),c_0_25]),c_0_26])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)
    | r2_hidden(esk3_2(esk7_0,esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))) = esk4_2(esk7_0,esk8_0)
    | r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)
    | k1_funct_1(esk8_0,esk3_2(esk7_0,esk8_0)) != esk4_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_71,plain,
    ( esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X2,esk3_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))) = esk4_2(esk7_0,esk8_0)
    | k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_63]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(X1,esk1_2(esk7_0,X1)) = esk2_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | k1_funct_1(X1,esk3_2(esk7_0,X1)) != esk4_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk3_2(esk7_0,X1),esk6_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_24]),c_0_23]),c_0_25]),c_0_26])])).

cnf(c_0_76,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | r2_hidden(esk3_2(esk7_0,esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_63])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | k1_funct_1(esk8_0,esk3_2(esk7_0,esk8_0)) = esk4_2(esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_63])).

cnf(c_0_78,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | esk1_2(X1,X2) != k1_funct_1(X1,esk2_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),esk5_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,X1)) != esk1_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk2_2(esk7_0,X1),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_45]),c_0_24]),c_0_23]),c_0_25]),c_0_26])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk2_2(esk7_0,esk8_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))) = esk1_2(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0)) != esk1_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0)) = esk1_2(esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_80])).

cnf(c_0_86,plain,
    ( X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X2,esk3_2(X1,X2))
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | esk1_2(X1,X2) != k1_funct_1(X1,esk2_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_88,negated_conjecture,
    ( X1 = k2_funct_1(esk7_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,X1)) != esk1_2(esk7_0,X1)
    | k1_funct_1(X1,esk3_2(esk7_0,X1)) != esk4_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk2_2(esk7_0,X1),esk5_0)
    | ~ r2_hidden(esk3_2(esk7_0,X1),esk6_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_45]),c_0_24]),c_0_24]),c_0_23]),c_0_25]),c_0_26])])).

cnf(c_0_89,negated_conjecture,
    ( k1_funct_1(esk8_0,esk3_2(esk7_0,esk8_0)) = esk4_2(esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_87]),c_0_63])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_87]),c_0_63])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_82]),c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_85]),c_0_89]),c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.19/0.39  # and selection function SelectComplexG.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t34_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))&![X5, X6]:(((r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6)=>(r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5))&((r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5)=>(r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_2)).
% 0.19/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.39  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 0.19/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))&![X5, X6]:(((r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6)=>(r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5))&((r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5)=>(r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t34_funct_2])).
% 0.19/0.39  fof(c_0_8, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k2_relset_1(X24,X25,X26)=k2_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.39  fof(c_0_9, negated_conjecture, ![X34, X35]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk5_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))))&(((k2_relset_1(esk5_0,esk6_0,esk7_0)=esk6_0&v2_funct_1(esk7_0))&(((r2_hidden(X35,esk5_0)|(~r2_hidden(X34,esk6_0)|k1_funct_1(esk8_0,X34)!=X35))&(k1_funct_1(esk7_0,X35)=X34|(~r2_hidden(X34,esk6_0)|k1_funct_1(esk8_0,X34)!=X35)))&((r2_hidden(X34,esk6_0)|(~r2_hidden(X35,esk5_0)|k1_funct_1(esk7_0,X35)!=X34))&(k1_funct_1(esk8_0,X34)=X35|(~r2_hidden(X35,esk5_0)|k1_funct_1(esk7_0,X35)!=X34)))))&((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk8_0!=k2_funct_1(esk7_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).
% 0.19/0.39  fof(c_0_10, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.39  fof(c_0_11, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.39  fof(c_0_12, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.39  fof(c_0_13, plain, ![X11, X12, X13, X14, X15, X16]:(((k1_relat_1(X12)=k2_relat_1(X11)|X12!=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(((r2_hidden(X14,k1_relat_1(X11))|(~r2_hidden(X13,k2_relat_1(X11))|X14!=k1_funct_1(X12,X13))|X12!=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(X13=k1_funct_1(X11,X14)|(~r2_hidden(X13,k2_relat_1(X11))|X14!=k1_funct_1(X12,X13))|X12!=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&((r2_hidden(X15,k2_relat_1(X11))|(~r2_hidden(X16,k1_relat_1(X11))|X15!=k1_funct_1(X11,X16))|X12!=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(X16=k1_funct_1(X12,X15)|(~r2_hidden(X16,k1_relat_1(X11))|X15!=k1_funct_1(X11,X16))|X12!=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))))&(((((r2_hidden(esk4_2(X11,X12),k1_relat_1(X11))|r2_hidden(esk1_2(X11,X12),k2_relat_1(X11))|k1_relat_1(X12)!=k2_relat_1(X11)|X12=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(esk3_2(X11,X12)=k1_funct_1(X11,esk4_2(X11,X12))|r2_hidden(esk1_2(X11,X12),k2_relat_1(X11))|k1_relat_1(X12)!=k2_relat_1(X11)|X12=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(esk3_2(X11,X12),k2_relat_1(X11))|esk4_2(X11,X12)!=k1_funct_1(X12,esk3_2(X11,X12))|r2_hidden(esk1_2(X11,X12),k2_relat_1(X11))|k1_relat_1(X12)!=k2_relat_1(X11)|X12=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(((r2_hidden(esk4_2(X11,X12),k1_relat_1(X11))|esk2_2(X11,X12)=k1_funct_1(X12,esk1_2(X11,X12))|k1_relat_1(X12)!=k2_relat_1(X11)|X12=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(esk3_2(X11,X12)=k1_funct_1(X11,esk4_2(X11,X12))|esk2_2(X11,X12)=k1_funct_1(X12,esk1_2(X11,X12))|k1_relat_1(X12)!=k2_relat_1(X11)|X12=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(esk3_2(X11,X12),k2_relat_1(X11))|esk4_2(X11,X12)!=k1_funct_1(X12,esk3_2(X11,X12))|esk2_2(X11,X12)=k1_funct_1(X12,esk1_2(X11,X12))|k1_relat_1(X12)!=k2_relat_1(X11)|X12=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))))&(((r2_hidden(esk4_2(X11,X12),k1_relat_1(X11))|(~r2_hidden(esk2_2(X11,X12),k1_relat_1(X11))|esk1_2(X11,X12)!=k1_funct_1(X11,esk2_2(X11,X12)))|k1_relat_1(X12)!=k2_relat_1(X11)|X12=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(esk3_2(X11,X12)=k1_funct_1(X11,esk4_2(X11,X12))|(~r2_hidden(esk2_2(X11,X12),k1_relat_1(X11))|esk1_2(X11,X12)!=k1_funct_1(X11,esk2_2(X11,X12)))|k1_relat_1(X12)!=k2_relat_1(X11)|X12=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(esk3_2(X11,X12),k2_relat_1(X11))|esk4_2(X11,X12)!=k1_funct_1(X12,esk3_2(X11,X12))|(~r2_hidden(esk2_2(X11,X12),k1_relat_1(X11))|esk1_2(X11,X12)!=k1_funct_1(X11,esk2_2(X11,X12)))|k1_relat_1(X12)!=k2_relat_1(X11)|X12=k2_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 0.19/0.39  cnf(c_0_14, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_16, negated_conjecture, (k2_relset_1(esk5_0,esk6_0,esk7_0)=esk6_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_17, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_18, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  fof(c_0_19, plain, ![X27, X28, X29]:((((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))))&((~v1_funct_2(X29,X27,X28)|X29=k1_xboole_0|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X29!=k1_xboole_0|v1_funct_2(X29,X27,X28)|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.39  cnf(c_0_20, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_22, plain, (esk3_2(X1,X2)=k1_funct_1(X1,esk4_2(X1,X2))|r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))|X2=k2_funct_1(X1)|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (k2_relat_1(esk7_0)=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_15]), c_0_18])])).
% 0.19/0.39  cnf(c_0_27, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (k1_relset_1(esk6_0,esk5_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X2,esk6_0)|k1_funct_1(esk8_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,X1))=esk3_2(esk7_0,X1)|X1=k2_funct_1(esk7_0)|r2_hidden(esk1_2(esk7_0,X1),esk6_0)|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_28]), c_0_29])]), c_0_30])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_21]), c_0_18])])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (esk8_0!=k2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_37, plain, (esk3_2(X1,X2)=k1_funct_1(X1,esk4_2(X1,X2))|esk2_2(X1,X2)=k1_funct_1(X2,esk1_2(X1,X2))|X2=k2_funct_1(X1)|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,X1),esk5_0)|~r2_hidden(X1,esk6_0)), inference(er,[status(thm)],[c_0_31])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))=esk3_2(esk7_0,esk8_0)|r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,X1))=esk3_2(esk7_0,X1)|k1_funct_1(X1,esk1_2(esk7_0,X1))=esk2_2(esk7_0,X1)|X1=k2_funct_1(esk7_0)|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_23]), c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.39  cnf(c_0_44, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))|X2=k2_funct_1(X1)|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_15]), c_0_38]), c_0_39])]), c_0_40])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk7_0,X1)=X2|~r2_hidden(X2,esk6_0)|k1_funct_1(esk8_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_47, plain, (esk3_2(X1,X2)=k1_funct_1(X1,esk4_2(X1,X2))|X2=k2_funct_1(X1)|~r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|esk1_2(X1,X2)!=k1_funct_1(X1,esk2_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))=esk3_2(esk7_0,esk8_0)|r2_hidden(k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)),esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))=esk2_2(esk7_0,esk8_0)|k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))=esk3_2(esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk5_0)|k1_funct_1(esk7_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (X1=k2_funct_1(esk7_0)|r2_hidden(esk4_2(esk7_0,X1),esk5_0)|r2_hidden(esk1_2(esk7_0,X1),esk6_0)|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_23]), c_0_24]), c_0_45]), c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk8_0,X1))=X1|~r2_hidden(X1,esk6_0)), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,X1))=esk3_2(esk7_0,X1)|X1=k2_funct_1(esk7_0)|k1_funct_1(esk7_0,esk2_2(esk7_0,X1))!=esk1_2(esk7_0,X1)|k1_relat_1(X1)!=esk6_0|~r2_hidden(esk2_2(esk7_0,X1),esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_45]), c_0_24]), c_0_23]), c_0_25]), c_0_26])])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))=esk3_2(esk7_0,esk8_0)|r2_hidden(esk2_2(esk7_0,esk8_0),esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),esk6_0)|~r2_hidden(X1,esk5_0)), inference(er,[status(thm)],[c_0_50])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)|r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)))=esk1_2(esk7_0,esk8_0)|k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))=esk3_2(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_52, c_0_42])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))=esk3_2(esk7_0,esk8_0)|k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0))!=esk1_2(esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.19/0.39  cnf(c_0_59, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|esk2_2(X1,X2)=k1_funct_1(X2,esk1_2(X1,X2))|X2=k2_funct_1(X1)|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (k1_funct_1(esk8_0,X1)=X2|~r2_hidden(X2,esk5_0)|k1_funct_1(esk7_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_61, plain, (r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))|X2=k2_funct_1(X1)|~r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))|esk4_2(X1,X2)!=k1_funct_1(X2,esk3_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)),esk6_0)|r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))=esk3_2(esk7_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_49]), c_0_58])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, (k1_funct_1(X1,esk1_2(esk7_0,X1))=esk2_2(esk7_0,X1)|X1=k2_funct_1(esk7_0)|r2_hidden(esk4_2(esk7_0,X1),esk5_0)|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_23]), c_0_45]), c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (k1_funct_1(esk8_0,k1_funct_1(esk7_0,X1))=X1|~r2_hidden(X1,esk5_0)), inference(er,[status(thm)],[c_0_60])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (X1=k2_funct_1(esk7_0)|r2_hidden(esk1_2(esk7_0,X1),esk6_0)|k1_funct_1(X1,esk3_2(esk7_0,X1))!=esk4_2(esk7_0,X1)|k1_relat_1(X1)!=esk6_0|~r2_hidden(esk3_2(esk7_0,X1),esk6_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_24]), c_0_23]), c_0_25]), c_0_26])])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)|r2_hidden(esk3_2(esk7_0,esk8_0),esk6_0)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))=esk2_2(esk7_0,esk8_0)|r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)))=esk4_2(esk7_0,esk8_0)|r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_65, c_0_56])).
% 0.19/0.39  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)|k1_funct_1(esk8_0,esk3_2(esk7_0,esk8_0))!=esk4_2(esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.19/0.39  cnf(c_0_71, plain, (esk2_2(X1,X2)=k1_funct_1(X2,esk1_2(X1,X2))|X2=k2_funct_1(X1)|~r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))|esk4_2(X1,X2)!=k1_funct_1(X2,esk3_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_72, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))=esk2_2(esk7_0,esk8_0)|r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)),esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_68])).
% 0.19/0.39  cnf(c_0_73, negated_conjecture, (k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)))=esk4_2(esk7_0,esk8_0)|k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))=esk2_2(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_65, c_0_68])).
% 0.19/0.39  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_63]), c_0_70])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (k1_funct_1(X1,esk1_2(esk7_0,X1))=esk2_2(esk7_0,X1)|X1=k2_funct_1(esk7_0)|k1_funct_1(X1,esk3_2(esk7_0,X1))!=esk4_2(esk7_0,X1)|k1_relat_1(X1)!=esk6_0|~r2_hidden(esk3_2(esk7_0,X1),esk6_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_24]), c_0_23]), c_0_25]), c_0_26])])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))=esk2_2(esk7_0,esk8_0)|r2_hidden(esk3_2(esk7_0,esk8_0),esk6_0)), inference(rw,[status(thm)],[c_0_72, c_0_63])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))=esk2_2(esk7_0,esk8_0)|k1_funct_1(esk8_0,esk3_2(esk7_0,esk8_0))=esk4_2(esk7_0,esk8_0)), inference(rw,[status(thm)],[c_0_73, c_0_63])).
% 0.19/0.39  cnf(c_0_78, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|X2=k2_funct_1(X1)|~r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|esk1_2(X1,X2)!=k1_funct_1(X1,esk2_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_79, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)),esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_74])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))=esk2_2(esk7_0,esk8_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_33]), c_0_34]), c_0_35])]), c_0_36]), c_0_77])).
% 0.19/0.39  cnf(c_0_81, negated_conjecture, (X1=k2_funct_1(esk7_0)|r2_hidden(esk4_2(esk7_0,X1),esk5_0)|k1_funct_1(esk7_0,esk2_2(esk7_0,X1))!=esk1_2(esk7_0,X1)|k1_relat_1(X1)!=esk6_0|~r2_hidden(esk2_2(esk7_0,X1),esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_45]), c_0_24]), c_0_23]), c_0_25]), c_0_26])])).
% 0.19/0.39  cnf(c_0_82, negated_conjecture, (r2_hidden(esk2_2(esk7_0,esk8_0),esk5_0)), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.39  cnf(c_0_83, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)))=esk1_2(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_52, c_0_74])).
% 0.19/0.39  cnf(c_0_84, negated_conjecture, (r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0)|k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0))!=esk1_2(esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.19/0.39  cnf(c_0_85, negated_conjecture, (k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0))=esk1_2(esk7_0,esk8_0)), inference(rw,[status(thm)],[c_0_83, c_0_80])).
% 0.19/0.39  cnf(c_0_86, plain, (X2=k2_funct_1(X1)|~r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))|esk4_2(X1,X2)!=k1_funct_1(X2,esk3_2(X1,X2))|~r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|esk1_2(X1,X2)!=k1_funct_1(X1,esk2_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_87, negated_conjecture, (r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])])).
% 0.19/0.39  cnf(c_0_88, negated_conjecture, (X1=k2_funct_1(esk7_0)|k1_funct_1(esk7_0,esk2_2(esk7_0,X1))!=esk1_2(esk7_0,X1)|k1_funct_1(X1,esk3_2(esk7_0,X1))!=esk4_2(esk7_0,X1)|k1_relat_1(X1)!=esk6_0|~r2_hidden(esk2_2(esk7_0,X1),esk5_0)|~r2_hidden(esk3_2(esk7_0,X1),esk6_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_45]), c_0_24]), c_0_24]), c_0_23]), c_0_25]), c_0_26])])).
% 0.19/0.39  cnf(c_0_89, negated_conjecture, (k1_funct_1(esk8_0,esk3_2(esk7_0,esk8_0))=esk4_2(esk7_0,esk8_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_87]), c_0_63])).
% 0.19/0.39  cnf(c_0_90, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk8_0),esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_87]), c_0_63])).
% 0.19/0.39  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_82]), c_0_33]), c_0_34]), c_0_35])]), c_0_36]), c_0_85]), c_0_89]), c_0_90])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 92
% 0.19/0.39  # Proof object clause steps            : 77
% 0.19/0.39  # Proof object formula steps           : 15
% 0.19/0.39  # Proof object conjectures             : 66
% 0.19/0.39  # Proof object clause conjectures      : 63
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 29
% 0.19/0.39  # Proof object initial formulas used   : 7
% 0.19/0.39  # Proof object generating inferences   : 37
% 0.19/0.39  # Proof object simplifying inferences  : 119
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 7
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 39
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 39
% 0.19/0.39  # Processed clauses                    : 349
% 0.19/0.39  # ...of these trivial                  : 27
% 0.19/0.39  # ...subsumed                          : 98
% 0.19/0.39  # ...remaining for further processing  : 223
% 0.19/0.39  # Other redundant clauses eliminated   : 18
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 95
% 0.19/0.39  # Generated clauses                    : 397
% 0.19/0.39  # ...of the previous two non-trivial   : 427
% 0.19/0.39  # Contextual simplify-reflections      : 3
% 0.19/0.39  # Paramodulations                      : 384
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 18
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 76
% 0.19/0.39  #    Positive orientable unit clauses  : 25
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 3
% 0.19/0.39  #    Non-unit-clauses                  : 48
% 0.19/0.39  # Current number of unprocessed clauses: 122
% 0.19/0.39  # ...number of literals in the above   : 308
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 134
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 3556
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1403
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 101
% 0.19/0.39  # Unit Clause-clause subsumption calls : 90
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 8
% 0.19/0.39  # BW rewrite match successes           : 8
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 13441
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.047 s
% 0.19/0.39  # System time              : 0.005 s
% 0.19/0.39  # Total time               : 0.053 s
% 0.19/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
