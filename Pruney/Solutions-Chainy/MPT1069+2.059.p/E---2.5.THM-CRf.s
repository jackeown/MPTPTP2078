%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:57 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 185 expanded)
%              Number of clauses        :   42 (  68 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  236 (1084 expanded)
%              Number of equality atoms :   58 ( 241 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & m1_subset_1(esk6_0,esk2_0)
    & r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0))
    & esk2_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0) != k7_partfun1(esk1_0,esk5_0,k1_funct_1(esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_16,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ v5_relat_1(X32,X31)
      | ~ v1_funct_1(X32)
      | ~ r2_hidden(X33,k1_relat_1(X32))
      | k7_partfun1(X31,X32,X33) = k1_funct_1(X32,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

fof(c_0_17,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_relset_1(X22,X23,X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_18,plain,(
    ! [X28,X29,X30] :
      ( ( ~ v1_funct_2(X30,X28,X29)
        | X28 = k1_relset_1(X28,X29,X30)
        | X29 = k1_xboole_0
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( X28 != k1_relset_1(X28,X29,X30)
        | v1_funct_2(X30,X28,X29)
        | X29 = k1_xboole_0
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( ~ v1_funct_2(X30,X28,X29)
        | X28 = k1_relset_1(X28,X29,X30)
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( X28 != k1_relset_1(X28,X29,X30)
        | v1_funct_2(X30,X28,X29)
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( ~ v1_funct_2(X30,X28,X29)
        | X30 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( X30 != k1_xboole_0
        | v1_funct_2(X30,X28,X29)
        | X28 = k1_xboole_0
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0) != k7_partfun1(esk1_0,esk5_0,k1_funct_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( v1_xboole_0(X36)
      | ~ v1_funct_1(X37)
      | ~ v1_funct_2(X37,X35,X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | ~ v1_funct_1(X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X34)))
      | ~ m1_subset_1(X39,X35)
      | ~ r1_tarski(k2_relset_1(X35,X36,X37),k1_relset_1(X36,X34,X38))
      | X35 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X35,X36,X34,X37,X38),X39) = k1_funct_1(X38,k1_funct_1(X37,X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_23,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X19,X20,X21] :
      ( ( v4_relat_1(X21,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v5_relat_1(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k2_relset_1(X25,X26,X27) = k2_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_31,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ v5_relat_1(esk5_0,esk1_0)
    | ~ v1_relat_1(esk5_0)
    | ~ r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_33,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk6_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_43,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v5_relat_1(X17,X16)
      | ~ v1_funct_1(X17)
      | ~ r2_hidden(X18,k1_relat_1(X17))
      | r2_hidden(k1_funct_1(X17,X18),X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

fof(c_0_44,plain,(
    ! [X12,X13] :
      ( ( ~ v5_relat_1(X13,X12)
        | r1_tarski(k2_relat_1(X13),X12)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_tarski(k2_relat_1(X13),X12)
        | v5_relat_1(X13,X12)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_46,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( ~ v5_relat_1(esk5_0,esk1_0)
    | ~ v1_relat_1(esk5_0)
    | ~ r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_21]),c_0_35]),c_0_26]),c_0_28]),c_0_36]),c_0_37])]),c_0_38]),c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_41])])).

cnf(c_0_51,negated_conjecture,
    ( v5_relat_1(esk5_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_28])).

cnf(c_0_52,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_41])])).

cnf(c_0_54,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_36])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_0)
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 = k1_relat_1(esk4_0)
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_36])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])]),c_0_51])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),X2)
    | ~ v5_relat_1(esk4_0,X2)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_53])])).

cnf(c_0_60,negated_conjecture,
    ( v5_relat_1(esk4_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_53])])).

fof(c_0_61,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | v1_xboole_0(k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_relat_1(esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:44:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.030 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 0.14/0.38  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.14/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.14/0.38  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.14/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.14/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.38  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 0.14/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.14/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.14/0.38  fof(c_0_15, negated_conjecture, (~v1_xboole_0(esk3_0)&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))))&(m1_subset_1(esk6_0,esk2_0)&(r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0))&(esk2_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0)!=k7_partfun1(esk1_0,esk5_0,k1_funct_1(esk4_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.14/0.38  fof(c_0_16, plain, ![X31, X32, X33]:(~v1_relat_1(X32)|~v5_relat_1(X32,X31)|~v1_funct_1(X32)|(~r2_hidden(X33,k1_relat_1(X32))|k7_partfun1(X31,X32,X33)=k1_funct_1(X32,X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.14/0.38  fof(c_0_17, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k1_relset_1(X22,X23,X24)=k1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.38  fof(c_0_18, plain, ![X28, X29, X30]:((((~v1_funct_2(X30,X28,X29)|X28=k1_relset_1(X28,X29,X30)|X29=k1_xboole_0|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(X28!=k1_relset_1(X28,X29,X30)|v1_funct_2(X30,X28,X29)|X29=k1_xboole_0|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))&((~v1_funct_2(X30,X28,X29)|X28=k1_relset_1(X28,X29,X30)|X28!=k1_xboole_0|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(X28!=k1_relset_1(X28,X29,X30)|v1_funct_2(X30,X28,X29)|X28!=k1_xboole_0|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))))&((~v1_funct_2(X30,X28,X29)|X30=k1_xboole_0|X28=k1_xboole_0|X29!=k1_xboole_0|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(X30!=k1_xboole_0|v1_funct_2(X30,X28,X29)|X28=k1_xboole_0|X29!=k1_xboole_0|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0)!=k7_partfun1(esk1_0,esk5_0,k1_funct_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_20, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  fof(c_0_22, plain, ![X34, X35, X36, X37, X38, X39]:(v1_xboole_0(X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X34)))|(~m1_subset_1(X39,X35)|(~r1_tarski(k2_relset_1(X35,X36,X37),k1_relset_1(X36,X34,X38))|(X35=k1_xboole_0|k1_funct_1(k8_funct_2(X35,X36,X34,X37,X38),X39)=k1_funct_1(X38,k1_funct_1(X37,X39)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.14/0.38  fof(c_0_23, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.38  fof(c_0_24, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.38  fof(c_0_25, plain, ![X19, X20, X21]:((v4_relat_1(X21,X19)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(v5_relat_1(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_27, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  fof(c_0_29, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k2_relset_1(X25,X26,X27)=k2_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.14/0.38  fof(c_0_30, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.38  cnf(c_0_31, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0)!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~v5_relat_1(esk5_0,esk1_0)|~v1_relat_1(esk5_0)|~r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.14/0.38  cnf(c_0_33, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk6_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_40, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_41, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_42, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  fof(c_0_43, plain, ![X16, X17, X18]:(~v1_relat_1(X17)|~v5_relat_1(X17,X16)|~v1_funct_1(X17)|(~r2_hidden(X18,k1_relat_1(X17))|r2_hidden(k1_funct_1(X17,X18),X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.14/0.38  fof(c_0_44, plain, ![X12, X13]:((~v5_relat_1(X13,X12)|r1_tarski(k2_relat_1(X13),X12)|~v1_relat_1(X13))&(~r1_tarski(k2_relat_1(X13),X12)|v5_relat_1(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.14/0.38  cnf(c_0_46, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_47, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_48, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_27, c_0_31])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (~v5_relat_1(esk5_0,esk1_0)|~v1_relat_1(esk5_0)|~r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_21]), c_0_35]), c_0_26]), c_0_28]), c_0_36]), c_0_37])]), c_0_38]), c_0_39])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_28]), c_0_41])])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (v5_relat_1(esk5_0,esk1_0)), inference(spm,[status(thm)],[c_0_42, c_0_28])).
% 0.14/0.38  cnf(c_0_52, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_41])])).
% 0.14/0.38  cnf(c_0_54, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_36])])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(esk6_0,esk2_0)|v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_37])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (esk2_0=k1_relat_1(esk4_0)|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_34]), c_0_36])])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (~r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])]), c_0_51])])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),X2)|~v5_relat_1(esk4_0,X2)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_35]), c_0_53])])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (v5_relat_1(esk4_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_53])])).
% 0.14/0.38  fof(c_0_61, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk6_0,k1_relat_1(esk4_0))|v1_xboole_0(k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (~r2_hidden(esk6_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.14/0.38  cnf(c_0_64, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (esk3_0=k1_xboole_0|v1_xboole_0(k1_relat_1(esk4_0))), inference(sr,[status(thm)],[c_0_62, c_0_63])).
% 0.14/0.38  cnf(c_0_66, negated_conjecture, (esk3_0=k1_xboole_0|k1_relat_1(esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_57])).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.14/0.38  cnf(c_0_68, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.38  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_67]), c_0_68])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 70
% 0.14/0.38  # Proof object clause steps            : 42
% 0.14/0.38  # Proof object formula steps           : 28
% 0.14/0.38  # Proof object conjectures             : 31
% 0.14/0.38  # Proof object clause conjectures      : 28
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 23
% 0.14/0.38  # Proof object initial formulas used   : 14
% 0.14/0.38  # Proof object generating inferences   : 16
% 0.14/0.38  # Proof object simplifying inferences  : 37
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 14
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 30
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 30
% 0.14/0.38  # Processed clauses                    : 111
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 5
% 0.14/0.38  # ...remaining for further processing  : 106
% 0.14/0.38  # Other redundant clauses eliminated   : 6
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 30
% 0.14/0.38  # Generated clauses                    : 65
% 0.14/0.38  # ...of the previous two non-trivial   : 63
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 59
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 6
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 40
% 0.14/0.38  #    Positive orientable unit clauses  : 12
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 25
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 62
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 613
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 238
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.38  # Unit Clause-clause subsumption calls : 12
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3556
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.036 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.040 s
% 0.14/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
