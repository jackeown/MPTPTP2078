%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:25 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 197 expanded)
%              Number of clauses        :   39 (  64 expanded)
%              Number of leaves         :   11 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  342 (1653 expanded)
%              Number of equality atoms :  103 ( 529 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
              & v2_funct_1(X3) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

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

fof(t22_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( X2 != k1_xboole_0
       => ( k2_relset_1(X1,X2,X3) = X2
        <=> ! [X4] :
              ( X4 != k1_xboole_0
             => ! [X5] :
                  ( ( v1_funct_1(X5)
                    & v1_funct_2(X5,X2,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) )
                 => ! [X6] :
                      ( ( v1_funct_1(X6)
                        & v1_funct_2(X6,X2,X4)
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) )
                     => ( r2_relset_1(X1,X4,k1_partfun1(X1,X2,X2,X4,X3,X5),k1_partfun1(X1,X2,X2,X4,X3,X6))
                       => r2_relset_1(X2,X4,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( ( k2_relset_1(X1,X2,X3) = X2
                & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
                & v2_funct_1(X3) )
             => ( X1 = k1_xboole_0
                | X2 = k1_xboole_0
                | X4 = k2_funct_1(X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_funct_2])).

fof(c_0_12,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X21 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != k1_xboole_0
        | v1_funct_2(X21,X19,X20)
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk4_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))
    & k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0
    & r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0))
    & v2_funct_1(esk6_0)
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk7_0 != k2_funct_1(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | k1_relset_1(X12,X13,X14) = k1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_15,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_21,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k1_relset_1(X1,X2,esk6_0) = esk4_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])])).

fof(c_0_23,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ( k2_relset_1(X29,X30,X31) != X30
        | X32 = k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X32)))
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X30,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X30,X32)))
        | ~ r2_relset_1(X29,X32,k1_partfun1(X29,X30,X30,X32,X31,X33),k1_partfun1(X29,X30,X30,X32,X31,X34))
        | r2_relset_1(X30,X32,X33,X34)
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( esk1_3(X29,X30,X31) != k1_xboole_0
        | k2_relset_1(X29,X30,X31) = X30
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v1_funct_1(esk2_3(X29,X30,X31))
        | k2_relset_1(X29,X30,X31) = X30
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v1_funct_2(esk2_3(X29,X30,X31),X30,esk1_3(X29,X30,X31))
        | k2_relset_1(X29,X30,X31) = X30
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( m1_subset_1(esk2_3(X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(X30,esk1_3(X29,X30,X31))))
        | k2_relset_1(X29,X30,X31) = X30
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v1_funct_1(esk3_3(X29,X30,X31))
        | k2_relset_1(X29,X30,X31) = X30
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v1_funct_2(esk3_3(X29,X30,X31),X30,esk1_3(X29,X30,X31))
        | k2_relset_1(X29,X30,X31) = X30
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( m1_subset_1(esk3_3(X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(X30,esk1_3(X29,X30,X31))))
        | k2_relset_1(X29,X30,X31) = X30
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( r2_relset_1(X29,esk1_3(X29,X30,X31),k1_partfun1(X29,X30,X30,esk1_3(X29,X30,X31),X31,esk2_3(X29,X30,X31)),k1_partfun1(X29,X30,X30,esk1_3(X29,X30,X31),X31,esk3_3(X29,X30,X31)))
        | k2_relset_1(X29,X30,X31) = X30
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ r2_relset_1(X30,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),esk3_3(X29,X30,X31))
        | k2_relset_1(X29,X30,X31) = X30
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_2])])])])])).

fof(c_0_26,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ~ v1_funct_1(X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k1_partfun1(X22,X23,X24,X25,X26,X27) = k5_relat_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_27,plain,(
    ! [X11] :
      ( ( k5_relat_1(X11,k2_funct_1(X11)) = k6_relat_1(k1_relat_1(X11))
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( k5_relat_1(k2_funct_1(X11),X11) = k6_relat_1(k2_relat_1(X11))
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_29,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X38,X39,X40] :
      ( ( v1_funct_1(k2_funct_1(X40))
        | ~ v2_funct_1(X40)
        | k2_relset_1(X38,X39,X40) != X39
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v1_funct_2(k2_funct_1(X40),X39,X38)
        | ~ v2_funct_1(X40)
        | k2_relset_1(X38,X39,X40) != X39
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( m1_subset_1(k2_funct_1(X40),k1_zfmisc_1(k2_zfmisc_1(X39,X38)))
        | ~ v2_funct_1(X40)
        | k2_relset_1(X38,X39,X40) != X39
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_32,plain,
    ( X4 = k1_xboole_0
    | r2_relset_1(X2,X4,X5,X6)
    | X2 = k1_xboole_0
    | k2_relset_1(X1,X2,X3) != X2
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X2,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r2_relset_1(X1,X4,k1_partfun1(X1,X2,X2,X4,X3,X5),k1_partfun1(X1,X2,X2,X4,X3,X6))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_30])])).

cnf(c_0_39,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_41,plain,(
    ! [X28] : k6_partfun1(X28) = k6_relat_1(X28) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_relset_1(X1,X2,X3,X4)
    | k2_relset_1(X5,X1,X6) != X1
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_2(X6,X5,X1)
    | ~ r2_relset_1(X5,X2,k1_partfun1(X5,X1,X1,X2,X6,X3),k5_relat_1(X6,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X1))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( k5_relat_1(esk6_0,k2_funct_1(esk6_0)) = k6_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_40]),c_0_17]),c_0_36]),c_0_37])])).

cnf(c_0_45,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_relset_1(X15,X16,X17,X18)
        | X17 = X18
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X17 != X18
        | r2_relset_1(X15,X16,X17,X18)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_48,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_relset_1(X2,X1,X3,k2_funct_1(esk6_0))
    | k2_relset_1(X4,X2,esk6_0) != X2
    | ~ v1_funct_2(k2_funct_1(esk6_0),X2,X1)
    | ~ v1_funct_2(esk6_0,X4,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ r2_relset_1(X4,X1,k1_partfun1(X4,X2,X2,X1,esk6_0,X3),k6_relat_1(esk4_0))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_37])])).

cnf(c_0_49,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r2_relset_1(esk5_0,esk4_0,esk7_0,k2_funct_1(esk6_0))
    | ~ v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_40]),c_0_17]),c_0_50]),c_0_51]),c_0_16]),c_0_52])]),c_0_53]),c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( esk7_0 != k2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_52])]),c_0_56])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_40]),c_0_17]),c_0_36]),c_0_37]),c_0_16])])).

cnf(c_0_60,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_40]),c_0_17]),c_0_36]),c_0_37]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.029 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.20/0.42  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.42  fof(t22_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(X2!=k1_xboole_0=>(k2_relset_1(X1,X2,X3)=X2<=>![X4]:(X4!=k1_xboole_0=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X2,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4))))=>(r2_relset_1(X1,X4,k1_partfun1(X1,X2,X2,X4,X3,X5),k1_partfun1(X1,X2,X2,X4,X3,X6))=>r2_relset_1(X2,X4,X5,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_2)).
% 0.20/0.42  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.20/0.42  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.20/0.42  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.42  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.42  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.42  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.20/0.42  fof(c_0_12, plain, ![X19, X20, X21]:((((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))))&((~v1_funct_2(X21,X19,X20)|X21=k1_xboole_0|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X21!=k1_xboole_0|v1_funct_2(X21,X19,X20)|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.42  fof(c_0_13, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk4_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))))&(((k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0&r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0)))&v2_funct_1(esk6_0))&((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk7_0!=k2_funct_1(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.42  fof(c_0_14, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|k1_relset_1(X12,X13,X14)=k1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.42  cnf(c_0_15, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_19, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_20, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.42  cnf(c_0_21, plain, (k1_relset_1(X1,X2,X3)=k1_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_19, c_0_19])).
% 0.20/0.42  cnf(c_0_22, negated_conjecture, (k1_relset_1(X1,X2,esk6_0)=esk4_0|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_16])])).
% 0.20/0.42  fof(c_0_23, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.42  fof(c_0_24, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.42  fof(c_0_25, plain, ![X29, X30, X31, X32, X33, X34]:((k2_relset_1(X29,X30,X31)!=X30|(X32=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X32)))|(~v1_funct_1(X34)|~v1_funct_2(X34,X30,X32)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X30,X32)))|(~r2_relset_1(X29,X32,k1_partfun1(X29,X30,X30,X32,X31,X33),k1_partfun1(X29,X30,X30,X32,X31,X34))|r2_relset_1(X30,X32,X33,X34)))))|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&((esk1_3(X29,X30,X31)!=k1_xboole_0|k2_relset_1(X29,X30,X31)=X30|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&((((v1_funct_1(esk2_3(X29,X30,X31))|k2_relset_1(X29,X30,X31)=X30|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&(v1_funct_2(esk2_3(X29,X30,X31),X30,esk1_3(X29,X30,X31))|k2_relset_1(X29,X30,X31)=X30|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))))&(m1_subset_1(esk2_3(X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(X30,esk1_3(X29,X30,X31))))|k2_relset_1(X29,X30,X31)=X30|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))))&((((v1_funct_1(esk3_3(X29,X30,X31))|k2_relset_1(X29,X30,X31)=X30|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&(v1_funct_2(esk3_3(X29,X30,X31),X30,esk1_3(X29,X30,X31))|k2_relset_1(X29,X30,X31)=X30|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))))&(m1_subset_1(esk3_3(X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(X30,esk1_3(X29,X30,X31))))|k2_relset_1(X29,X30,X31)=X30|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))))&((r2_relset_1(X29,esk1_3(X29,X30,X31),k1_partfun1(X29,X30,X30,esk1_3(X29,X30,X31),X31,esk2_3(X29,X30,X31)),k1_partfun1(X29,X30,X30,esk1_3(X29,X30,X31),X31,esk3_3(X29,X30,X31)))|k2_relset_1(X29,X30,X31)=X30|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&(~r2_relset_1(X30,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),esk3_3(X29,X30,X31))|k2_relset_1(X29,X30,X31)=X30|X30=k1_xboole_0|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_2])])])])])).
% 0.20/0.42  fof(c_0_26, plain, ![X22, X23, X24, X25, X26, X27]:(~v1_funct_1(X26)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|~v1_funct_1(X27)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k1_partfun1(X22,X23,X24,X25,X26,X27)=k5_relat_1(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.20/0.42  fof(c_0_27, plain, ![X11]:((k5_relat_1(X11,k2_funct_1(X11))=k6_relat_1(k1_relat_1(X11))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(k5_relat_1(k2_funct_1(X11),X11)=k6_relat_1(k2_relat_1(X11))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.20/0.42  cnf(c_0_29, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_30, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  fof(c_0_31, plain, ![X38, X39, X40]:(((v1_funct_1(k2_funct_1(X40))|(~v2_funct_1(X40)|k2_relset_1(X38,X39,X40)!=X39)|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&(v1_funct_2(k2_funct_1(X40),X39,X38)|(~v2_funct_1(X40)|k2_relset_1(X38,X39,X40)!=X39)|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))))&(m1_subset_1(k2_funct_1(X40),k1_zfmisc_1(k2_zfmisc_1(X39,X38)))|(~v2_funct_1(X40)|k2_relset_1(X38,X39,X40)!=X39)|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.20/0.42  cnf(c_0_32, plain, (X4=k1_xboole_0|r2_relset_1(X2,X4,X5,X6)|X2=k1_xboole_0|k2_relset_1(X1,X2,X3)!=X2|~v1_funct_1(X5)|~v1_funct_2(X5,X2,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~r2_relset_1(X1,X4,k1_partfun1(X1,X2,X2,X4,X3,X5),k1_partfun1(X1,X2,X2,X4,X3,X6))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_33, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  cnf(c_0_34, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(spm,[status(thm)],[c_0_28, c_0_16])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_16]), c_0_30])])).
% 0.20/0.42  cnf(c_0_39, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  fof(c_0_41, plain, ![X28]:k6_partfun1(X28)=k6_relat_1(X28), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.42  cnf(c_0_42, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r2_relset_1(X1,X2,X3,X4)|k2_relset_1(X5,X1,X6)!=X1|~v1_funct_2(X4,X1,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_2(X6,X5,X1)|~r2_relset_1(X5,X2,k1_partfun1(X5,X1,X1,X2,X6,X3),k5_relat_1(X6,X4))|~v1_funct_1(X4)|~v1_funct_1(X3)|~v1_funct_1(X6)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X1)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (k5_relat_1(esk6_0,k2_funct_1(esk6_0))=k6_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38])])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_16]), c_0_40]), c_0_17]), c_0_36]), c_0_37])])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_46, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  fof(c_0_47, plain, ![X15, X16, X17, X18]:((~r2_relset_1(X15,X16,X17,X18)|X17=X18|(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&(X17!=X18|r2_relset_1(X15,X16,X17,X18)|(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.42  cnf(c_0_48, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|r2_relset_1(X2,X1,X3,k2_funct_1(esk6_0))|k2_relset_1(X4,X2,esk6_0)!=X2|~v1_funct_2(k2_funct_1(esk6_0),X2,X1)|~v1_funct_2(esk6_0,X4,X2)|~v1_funct_2(X3,X2,X1)|~r2_relset_1(X4,X1,k1_partfun1(X4,X2,X2,X1,esk6_0,X3),k6_relat_1(esk4_0))|~v1_funct_1(X3)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_37])])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.42  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_54, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.42  cnf(c_0_55, negated_conjecture, (r2_relset_1(esk5_0,esk4_0,esk7_0,k2_funct_1(esk6_0))|~v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_40]), c_0_17]), c_0_50]), c_0_51]), c_0_16]), c_0_52])]), c_0_53]), c_0_18])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (esk7_0!=k2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (~v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_52])]), c_0_56])).
% 0.20/0.42  cnf(c_0_58, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, (~v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_40]), c_0_17]), c_0_36]), c_0_37]), c_0_16])])).
% 0.20/0.42  cnf(c_0_60, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_40]), c_0_17]), c_0_36]), c_0_37]), c_0_16])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 62
% 0.20/0.42  # Proof object clause steps            : 39
% 0.20/0.42  # Proof object formula steps           : 23
% 0.20/0.42  # Proof object conjectures             : 28
% 0.20/0.42  # Proof object clause conjectures      : 25
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 24
% 0.20/0.42  # Proof object initial formulas used   : 11
% 0.20/0.42  # Proof object generating inferences   : 14
% 0.20/0.42  # Proof object simplifying inferences  : 44
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 11
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 40
% 0.20/0.42  # Removed in clause preprocessing      : 1
% 0.20/0.42  # Initial clauses in saturation        : 39
% 0.20/0.42  # Processed clauses                    : 374
% 0.20/0.42  # ...of these trivial                  : 0
% 0.20/0.42  # ...subsumed                          : 106
% 0.20/0.42  # ...remaining for further processing  : 268
% 0.20/0.42  # Other redundant clauses eliminated   : 6
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 6
% 0.20/0.42  # Backward-rewritten                   : 4
% 0.20/0.42  # Generated clauses                    : 506
% 0.20/0.42  # ...of the previous two non-trivial   : 476
% 0.20/0.42  # Contextual simplify-reflections      : 190
% 0.20/0.42  # Paramodulations                      : 501
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 6
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 214
% 0.20/0.42  #    Positive orientable unit clauses  : 22
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 4
% 0.20/0.42  #    Non-unit-clauses                  : 188
% 0.20/0.42  # Current number of unprocessed clauses: 178
% 0.20/0.42  # ...number of literals in the above   : 1434
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 50
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 14289
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 2071
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 297
% 0.20/0.42  # Unit Clause-clause subsumption calls : 148
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 5
% 0.20/0.42  # BW rewrite match successes           : 3
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 35760
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.076 s
% 0.20/0.42  # System time              : 0.005 s
% 0.20/0.42  # Total time               : 0.081 s
% 0.20/0.42  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
