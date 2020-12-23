%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 198 expanded)
%              Number of clauses        :   48 (  76 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  252 (1095 expanded)
%              Number of equality atoms :   64 ( 232 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t186_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t185_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k1_funct_1(X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ! [X5] :
                ( ( v1_funct_1(X5)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                     => ( X2 = k1_xboole_0
                        | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t186_funct_2])).

fof(c_0_16,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k2_relset_1(X30,X31,X32) = k2_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))
    & m1_subset_1(esk8_0,esk4_0)
    & r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0))
    & esk4_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0) != k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k1_relset_1(X27,X28,X29) = k1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_20,plain,(
    ! [X19,X20] : v1_relat_1(k2_zfmisc_1(X19,X20)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_21,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v5_relat_1(X22,X21)
      | ~ v1_funct_1(X22)
      | ~ r2_hidden(X23,k1_relat_1(X22))
      | r2_hidden(k1_funct_1(X22,X23),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_24,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X17,X18] :
      ( ( ~ v5_relat_1(X18,X17)
        | r1_tarski(k2_relat_1(X18),X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r1_tarski(k2_relat_1(X18),X17)
        | v5_relat_1(X18,X17)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_30,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( v1_xboole_0(X41)
      | ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,X40,X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | ~ v1_funct_1(X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X39)))
      | ~ m1_subset_1(X44,X40)
      | ~ r1_tarski(k2_relset_1(X40,X41,X42),k1_relset_1(X41,X39,X43))
      | X40 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X40,X41,X39,X42,X43),X44) = k1_funct_1(X43,k1_funct_1(X42,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_relset_1(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_26])])).

cnf(c_0_35,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_37,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v1_funct_2(X35,X33,X34)
        | X33 = k1_relset_1(X33,X34,X35)
        | X34 = k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X33 != k1_relset_1(X33,X34,X35)
        | v1_funct_2(X35,X33,X34)
        | X34 = k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( ~ v1_funct_2(X35,X33,X34)
        | X33 = k1_relset_1(X33,X34,X35)
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X33 != k1_relset_1(X33,X34,X35)
        | v1_funct_2(X35,X33,X34)
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( ~ v1_funct_2(X35,X33,X34)
        | X35 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X35 != k1_xboole_0
        | v1_funct_2(X35,X33,X34)
        | X33 = k1_xboole_0
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_38,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_39,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_40,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | X3 = k1_xboole_0
    | k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6) = k1_funct_1(X4,k1_funct_1(X2,X6))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ m1_subset_1(X6,X3)
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_45,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v5_relat_1(X37,X36)
      | ~ v1_funct_1(X37)
      | ~ r2_hidden(X38,k1_relat_1(X37))
      | k7_partfun1(X36,X37,X38) = k1_funct_1(X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

fof(c_0_46,plain,(
    ! [X24,X25,X26] :
      ( ( v4_relat_1(X26,X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v5_relat_1(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),X2)
    | ~ v5_relat_1(esk6_0,X2)
    | ~ r2_hidden(X1,k1_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_48,negated_conjecture,
    ( v5_relat_1(esk6_0,k1_relset_1(esk5_0,esk3_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_34])])).

cnf(c_0_49,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk8_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk5_0,esk3_0,X2,esk7_0),X3) = k1_funct_1(esk7_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk5_0)
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(k2_relset_1(X1,esk5_0,X2),k1_relset_1(esk5_0,esk3_0,esk7_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))
    | ~ m1_subset_1(X3,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_relset_1(esk5_0,esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_42]),c_0_26])])).

cnf(c_0_60,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),k1_relset_1(esk5_0,esk3_0,esk7_0))
    | ~ r2_hidden(X1,k1_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_22]),c_0_50])])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk8_0,esk4_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),X1) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_33]),c_0_29]),c_0_36]),c_0_22])]),c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( k7_partfun1(X1,esk7_0,X2) = k1_funct_1(esk7_0,X2)
    | ~ v5_relat_1(esk7_0,X1)
    | ~ r2_hidden(X2,k1_relset_1(esk5_0,esk3_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_43]),c_0_59])])).

cnf(c_0_67,negated_conjecture,
    ( v5_relat_1(esk7_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_42])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,X1),k1_relset_1(esk5_0,esk3_0,esk7_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk8_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0) != k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_54])).

cnf(c_0_72,negated_conjecture,
    ( k7_partfun1(esk3_0,esk7_0,X1) = k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,k1_relset_1(esk5_0,esk3_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,esk8_0),k1_relset_1(esk5_0,esk3_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)) != k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_76,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_75]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.39  # and selection function SelectNewComplexAHP.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 0.20/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.39  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 0.20/0.39  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.39  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 0.20/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.39  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 0.20/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.39  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.20/0.39  fof(c_0_16, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k2_relset_1(X30,X31,X32)=k2_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.39  fof(c_0_17, negated_conjecture, (~v1_xboole_0(esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&((v1_funct_1(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(m1_subset_1(esk8_0,esk4_0)&(r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0))&(esk4_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0)!=k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.39  fof(c_0_18, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k1_relset_1(X27,X28,X29)=k1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.39  fof(c_0_19, plain, ![X15, X16]:(~v1_relat_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_relat_1(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.39  fof(c_0_20, plain, ![X19, X20]:v1_relat_1(k2_zfmisc_1(X19,X20)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.39  cnf(c_0_21, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  fof(c_0_23, plain, ![X21, X22, X23]:(~v1_relat_1(X22)|~v5_relat_1(X22,X21)|~v1_funct_1(X22)|(~r2_hidden(X23,k1_relat_1(X22))|r2_hidden(k1_funct_1(X22,X23),X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.20/0.39  cnf(c_0_24, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_25, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_26, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  fof(c_0_27, plain, ![X17, X18]:((~v5_relat_1(X18,X17)|r1_tarski(k2_relat_1(X18),X17)|~v1_relat_1(X18))&(~r1_tarski(k2_relat_1(X18),X17)|v5_relat_1(X18,X17)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.39  fof(c_0_30, plain, ![X39, X40, X41, X42, X43, X44]:(v1_xboole_0(X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X39)))|(~m1_subset_1(X44,X40)|(~r1_tarski(k2_relset_1(X40,X41,X42),k1_relset_1(X41,X39,X43))|(X40=k1_xboole_0|k1_funct_1(k8_funct_2(X40,X41,X39,X42,X43),X44)=k1_funct_1(X43,k1_funct_1(X42,X44)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.20/0.39  cnf(c_0_31, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (k1_relat_1(esk6_0)=k1_relset_1(esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_22]), c_0_26])])).
% 0.20/0.39  cnf(c_0_35, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k1_relset_1(esk5_0,esk3_0,esk7_0))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.39  fof(c_0_37, plain, ![X33, X34, X35]:((((~v1_funct_2(X35,X33,X34)|X33=k1_relset_1(X33,X34,X35)|X34=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(X33!=k1_relset_1(X33,X34,X35)|v1_funct_2(X35,X33,X34)|X34=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))&((~v1_funct_2(X35,X33,X34)|X33=k1_relset_1(X33,X34,X35)|X33!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(X33!=k1_relset_1(X33,X34,X35)|v1_funct_2(X35,X33,X34)|X33!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))))&((~v1_funct_2(X35,X33,X34)|X35=k1_xboole_0|X33=k1_xboole_0|X34!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(X35!=k1_xboole_0|v1_funct_2(X35,X33,X34)|X33=k1_xboole_0|X34!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.39  fof(c_0_38, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.39  fof(c_0_39, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.39  fof(c_0_40, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.39  cnf(c_0_41, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  fof(c_0_45, plain, ![X36, X37, X38]:(~v1_relat_1(X37)|~v5_relat_1(X37,X36)|~v1_funct_1(X37)|(~r2_hidden(X38,k1_relat_1(X37))|k7_partfun1(X36,X37,X38)=k1_funct_1(X37,X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.20/0.39  fof(c_0_46, plain, ![X24, X25, X26]:((v4_relat_1(X26,X24)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(v5_relat_1(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),X2)|~v5_relat_1(esk6_0,X2)|~r2_hidden(X1,k1_relset_1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (v5_relat_1(esk6_0,k1_relset_1(esk5_0,esk3_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_34])])).
% 0.20/0.39  cnf(c_0_49, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_51, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_52, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.39  cnf(c_0_53, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk8_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk5_0,esk3_0,X2,esk7_0),X3)=k1_funct_1(esk7_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk5_0)|~v1_funct_1(X2)|~r1_tarski(k2_relset_1(X1,esk5_0,X2),k1_relset_1(esk5_0,esk3_0,esk7_0))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))|~m1_subset_1(X3,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])]), c_0_44])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_57, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (k1_relat_1(esk7_0)=k1_relset_1(esk5_0,esk3_0,esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_42])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_42]), c_0_26])])).
% 0.20/0.39  cnf(c_0_60, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),k1_relset_1(esk5_0,esk3_0,esk7_0))|~r2_hidden(X1,k1_relset_1(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=esk4_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_22]), c_0_50])])).
% 0.20/0.39  cnf(c_0_63, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (r2_hidden(esk8_0,esk4_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),X1)=k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_50]), c_0_33]), c_0_29]), c_0_36]), c_0_22])]), c_0_56])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (k7_partfun1(X1,esk7_0,X2)=k1_funct_1(esk7_0,X2)|~v5_relat_1(esk7_0,X1)|~r2_hidden(X2,k1_relset_1(esk5_0,esk3_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_43]), c_0_59])])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (v5_relat_1(esk7_0,esk3_0)), inference(spm,[status(thm)],[c_0_60, c_0_42])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,X1),k1_relset_1(esk5_0,esk3_0,esk7_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (r2_hidden(esk8_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_56])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0)!=k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk5_0,esk3_0,esk6_0,esk7_0),esk8_0)=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_65, c_0_54])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (k7_partfun1(esk3_0,esk7_0,X1)=k1_funct_1(esk7_0,X1)|~r2_hidden(X1,k1_relset_1(esk5_0,esk3_0,esk7_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,esk8_0),k1_relset_1(esk5_0,esk3_0,esk7_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (k7_partfun1(esk3_0,esk7_0,k1_funct_1(esk6_0,esk8_0))!=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.20/0.39  cnf(c_0_76, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_75]), c_0_76])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 78
% 0.20/0.39  # Proof object clause steps            : 48
% 0.20/0.39  # Proof object formula steps           : 30
% 0.20/0.39  # Proof object conjectures             : 36
% 0.20/0.39  # Proof object clause conjectures      : 33
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 24
% 0.20/0.39  # Proof object initial formulas used   : 15
% 0.20/0.39  # Proof object generating inferences   : 21
% 0.20/0.39  # Proof object simplifying inferences  : 30
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 15
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 32
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 32
% 0.20/0.39  # Processed clauses                    : 201
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 39
% 0.20/0.39  # ...remaining for further processing  : 162
% 0.20/0.39  # Other redundant clauses eliminated   : 5
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 84
% 0.20/0.39  # Generated clauses                    : 147
% 0.20/0.39  # ...of the previous two non-trivial   : 197
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 143
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 5
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 42
% 0.20/0.39  #    Positive orientable unit clauses  : 13
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 26
% 0.20/0.39  # Current number of unprocessed clauses: 9
% 0.20/0.39  # ...number of literals in the above   : 18
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 116
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1039
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 519
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 32
% 0.20/0.39  # Unit Clause-clause subsumption calls : 32
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 5
% 0.20/0.39  # BW rewrite match successes           : 5
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 5461
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.040 s
% 0.20/0.39  # System time              : 0.003 s
% 0.20/0.39  # Total time               : 0.043 s
% 0.20/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
