%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:46 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 (1310 expanded)
%              Number of clauses        :   67 ( 676 expanded)
%              Number of leaves         :   10 ( 280 expanded)
%              Depth                    :   18
%              Number of atoms          :  298 (9988 expanded)
%              Number of equality atoms :  101 (3904 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(t121_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_10,plain,(
    ! [X25,X26,X27,X28,X30,X31,X32,X33,X34,X36] :
      ( ( v1_relat_1(esk1_4(X25,X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k1_funct_2(X25,X26) )
      & ( v1_funct_1(esk1_4(X25,X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k1_funct_2(X25,X26) )
      & ( X28 = esk1_4(X25,X26,X27,X28)
        | ~ r2_hidden(X28,X27)
        | X27 != k1_funct_2(X25,X26) )
      & ( k1_relat_1(esk1_4(X25,X26,X27,X28)) = X25
        | ~ r2_hidden(X28,X27)
        | X27 != k1_funct_2(X25,X26) )
      & ( r1_tarski(k2_relat_1(esk1_4(X25,X26,X27,X28)),X26)
        | ~ r2_hidden(X28,X27)
        | X27 != k1_funct_2(X25,X26) )
      & ( ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31)
        | X30 != X31
        | k1_relat_1(X31) != X25
        | ~ r1_tarski(k2_relat_1(X31),X26)
        | r2_hidden(X30,X27)
        | X27 != k1_funct_2(X25,X26) )
      & ( ~ r2_hidden(esk2_3(X32,X33,X34),X34)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | esk2_3(X32,X33,X34) != X36
        | k1_relat_1(X36) != X32
        | ~ r1_tarski(k2_relat_1(X36),X33)
        | X34 = k1_funct_2(X32,X33) )
      & ( v1_relat_1(esk3_3(X32,X33,X34))
        | r2_hidden(esk2_3(X32,X33,X34),X34)
        | X34 = k1_funct_2(X32,X33) )
      & ( v1_funct_1(esk3_3(X32,X33,X34))
        | r2_hidden(esk2_3(X32,X33,X34),X34)
        | X34 = k1_funct_2(X32,X33) )
      & ( esk2_3(X32,X33,X34) = esk3_3(X32,X33,X34)
        | r2_hidden(esk2_3(X32,X33,X34),X34)
        | X34 = k1_funct_2(X32,X33) )
      & ( k1_relat_1(esk3_3(X32,X33,X34)) = X32
        | r2_hidden(esk2_3(X32,X33,X34),X34)
        | X34 = k1_funct_2(X32,X33) )
      & ( r1_tarski(k2_relat_1(esk3_3(X32,X33,X34)),X33)
        | r2_hidden(esk2_3(X32,X33,X34),X34)
        | X34 = k1_funct_2(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_11,plain,
    ( v1_funct_1(esk1_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_12,plain,
    ( X1 = esk1_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_14,plain,
    ( v1_funct_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( esk1_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))
    & ( ~ v1_funct_1(esk6_0)
      | ~ v1_funct_2(esk6_0,esk4_0,esk5_0)
      | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_17,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( v1_relat_1(esk1_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( k1_relat_1(esk1_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_22,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ r1_tarski(k1_relat_1(X21),X19)
      | ~ r1_tarski(k2_relat_1(X21),X20)
      | m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_23,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_funct_1(esk6_0)
    | ~ v1_funct_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( v1_relat_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v1_funct_2(X24,X22,X23)
        | X22 = k1_relset_1(X22,X23,X24)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X22 != k1_relset_1(X22,X23,X24)
        | v1_funct_2(X24,X22,X23)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ v1_funct_2(X24,X22,X23)
        | X22 = k1_relset_1(X22,X23,X24)
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X22 != k1_relset_1(X22,X23,X24)
        | v1_funct_2(X24,X22,X23)
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ v1_funct_2(X24,X22,X23)
        | X24 = k1_xboole_0
        | X22 = k1_xboole_0
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X24 != k1_xboole_0
        | v1_funct_2(X24,X22,X23)
        | X22 = k1_xboole_0
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_28,plain,
    ( k1_relat_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(esk1_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_35,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_relat_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k1_relat_1(X3),X1)
    | ~ r1_tarski(k2_relat_1(X3),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk4_0,esk5_0)
    | ~ v1_relat_1(esk6_0)
    | ~ r1_tarski(k1_relat_1(esk6_0),esk4_0)
    | ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X2),X3)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_45,plain,
    ( k1_relset_1(k1_relat_1(X1),X2,X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk4_0,esk5_0)
    | ~ r1_tarski(k1_relat_1(esk6_0),esk4_0)
    | ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

fof(c_0_47,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_48,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk6_0,X2,X1)
    | k1_relset_1(X2,X1,esk6_0) != X2
    | ~ r1_tarski(k2_relat_1(esk6_0),X1)
    | ~ r1_tarski(esk4_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_41])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( k1_relset_1(esk4_0,X1,esk6_0) = esk4_0
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_41])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk4_0,esk5_0)
    | ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_43]),c_0_39])])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_funct_2(esk6_0,X1,esk5_0)
    | k1_relset_1(X1,esk5_0,esk6_0) != X1
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_49])])).

fof(c_0_57,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_58,plain,(
    ! [X13,X14,X15] :
      ( ( v4_relat_1(X15,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v5_relat_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | ~ r1_tarski(esk5_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_39])]),c_0_56])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_63,plain,(
    ! [X11,X12] :
      ( ( ~ v4_relat_1(X12,X11)
        | r1_tarski(k1_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k1_relat_1(X12),X11)
        | v4_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_64,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_61]),c_0_62])])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_41]),c_0_62]),c_0_43])])).

cnf(c_0_71,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_39])).

cnf(c_0_75,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_71]),c_0_72])).

cnf(c_0_76,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_72])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_72])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_62])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_43]),c_0_41])])).

cnf(c_0_80,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_49]),c_0_41]),c_0_43])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_61])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(esk6_0,k1_xboole_0,X1)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_43]),c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(esk6_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_79])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:05:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.21/0.39  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.21/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.39  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.21/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.39  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.39  fof(c_0_10, plain, ![X25, X26, X27, X28, X30, X31, X32, X33, X34, X36]:(((((((v1_relat_1(esk1_4(X25,X26,X27,X28))|~r2_hidden(X28,X27)|X27!=k1_funct_2(X25,X26))&(v1_funct_1(esk1_4(X25,X26,X27,X28))|~r2_hidden(X28,X27)|X27!=k1_funct_2(X25,X26)))&(X28=esk1_4(X25,X26,X27,X28)|~r2_hidden(X28,X27)|X27!=k1_funct_2(X25,X26)))&(k1_relat_1(esk1_4(X25,X26,X27,X28))=X25|~r2_hidden(X28,X27)|X27!=k1_funct_2(X25,X26)))&(r1_tarski(k2_relat_1(esk1_4(X25,X26,X27,X28)),X26)|~r2_hidden(X28,X27)|X27!=k1_funct_2(X25,X26)))&(~v1_relat_1(X31)|~v1_funct_1(X31)|X30!=X31|k1_relat_1(X31)!=X25|~r1_tarski(k2_relat_1(X31),X26)|r2_hidden(X30,X27)|X27!=k1_funct_2(X25,X26)))&((~r2_hidden(esk2_3(X32,X33,X34),X34)|(~v1_relat_1(X36)|~v1_funct_1(X36)|esk2_3(X32,X33,X34)!=X36|k1_relat_1(X36)!=X32|~r1_tarski(k2_relat_1(X36),X33))|X34=k1_funct_2(X32,X33))&(((((v1_relat_1(esk3_3(X32,X33,X34))|r2_hidden(esk2_3(X32,X33,X34),X34)|X34=k1_funct_2(X32,X33))&(v1_funct_1(esk3_3(X32,X33,X34))|r2_hidden(esk2_3(X32,X33,X34),X34)|X34=k1_funct_2(X32,X33)))&(esk2_3(X32,X33,X34)=esk3_3(X32,X33,X34)|r2_hidden(esk2_3(X32,X33,X34),X34)|X34=k1_funct_2(X32,X33)))&(k1_relat_1(esk3_3(X32,X33,X34))=X32|r2_hidden(esk2_3(X32,X33,X34),X34)|X34=k1_funct_2(X32,X33)))&(r1_tarski(k2_relat_1(esk3_3(X32,X33,X34)),X33)|r2_hidden(esk2_3(X32,X33,X34),X34)|X34=k1_funct_2(X32,X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.21/0.39  cnf(c_0_11, plain, (v1_funct_1(esk1_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_12, plain, (X1=esk1_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.21/0.39  cnf(c_0_14, plain, (v1_funct_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_15, plain, (esk1_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_12])).
% 0.21/0.39  fof(c_0_16, negated_conjecture, (r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))&(~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.21/0.39  cnf(c_0_17, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, (r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_19, plain, (v1_relat_1(esk1_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_20, plain, (k1_relat_1(esk1_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  fof(c_0_21, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.39  fof(c_0_22, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|(~r1_tarski(k1_relat_1(X21),X19)|~r1_tarski(k2_relat_1(X21),X20)|m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.21/0.39  fof(c_0_23, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.39  cnf(c_0_26, plain, (v1_relat_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.21/0.39  fof(c_0_27, plain, ![X22, X23, X24]:((((~v1_funct_2(X24,X22,X23)|X22=k1_relset_1(X22,X23,X24)|X23=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(X22!=k1_relset_1(X22,X23,X24)|v1_funct_2(X24,X22,X23)|X23=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&((~v1_funct_2(X24,X22,X23)|X22=k1_relset_1(X22,X23,X24)|X22!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(X22!=k1_relset_1(X22,X23,X24)|v1_funct_2(X24,X22,X23)|X22!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))))&((~v1_funct_2(X24,X22,X23)|X24=k1_xboole_0|X22=k1_xboole_0|X23!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(X24!=k1_xboole_0|v1_funct_2(X24,X22,X23)|X22=k1_xboole_0|X23!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.39  cnf(c_0_28, plain, (k1_relat_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_29, plain, (r1_tarski(k2_relat_1(esk1_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (~v1_funct_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.21/0.39  cnf(c_0_34, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_15])).
% 0.21/0.39  cnf(c_0_35, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_36, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_28, c_0_15])).
% 0.21/0.39  cnf(c_0_37, plain, (r1_tarski(k2_relat_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_38, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~v1_relat_1(X3)|~r1_tarski(k1_relat_1(X3),X1)|~r1_tarski(k2_relat_1(X3),X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.39  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (~v1_funct_2(esk6_0,esk4_0,esk5_0)|~v1_relat_1(esk6_0)|~r1_tarski(k1_relat_1(esk6_0),esk4_0)|~r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_18])).
% 0.21/0.39  cnf(c_0_42, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X2),X3)|~r1_tarski(k2_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_35, c_0_31])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(spm,[status(thm)],[c_0_36, c_0_18])).
% 0.21/0.39  cnf(c_0_44, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_37, c_0_15])).
% 0.21/0.39  cnf(c_0_45, plain, (k1_relset_1(k1_relat_1(X1),X2,X1)=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (~v1_funct_2(esk6_0,esk4_0,esk5_0)|~r1_tarski(k1_relat_1(esk6_0),esk4_0)|~r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.21/0.39  fof(c_0_47, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk6_0,X2,X1)|k1_relset_1(X2,X1,esk6_0)!=X2|~r1_tarski(k2_relat_1(esk6_0),X1)|~r1_tarski(esk4_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_41])])).
% 0.21/0.39  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_18])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (k1_relset_1(esk4_0,X1,esk6_0)=esk4_0|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_43]), c_0_41])])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (~v1_funct_2(esk6_0,esk4_0,esk5_0)|~r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_43]), c_0_39])])).
% 0.21/0.39  cnf(c_0_52, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_53, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (esk5_0=k1_xboole_0|v1_funct_2(esk6_0,X1,esk5_0)|k1_relset_1(X1,esk5_0,esk6_0)!=X1|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.39  cnf(c_0_55, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=esk4_0), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (~v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_49])])).
% 0.21/0.39  fof(c_0_57, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.39  fof(c_0_58, plain, ![X13, X14, X15]:((v4_relat_1(X15,X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))&(v5_relat_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.39  cnf(c_0_59, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_52])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0|~r1_tarski(esk5_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_53, c_0_49])).
% 0.21/0.39  cnf(c_0_61, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_39])]), c_0_56])).
% 0.21/0.39  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.39  fof(c_0_63, plain, ![X11, X12]:((~v4_relat_1(X12,X11)|r1_tarski(k1_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k1_relat_1(X12),X11)|v4_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.39  cnf(c_0_64, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.21/0.39  cnf(c_0_65, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_xboole_0)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_59])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_61]), c_0_62])])).
% 0.21/0.39  cnf(c_0_67, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_68, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.39  cnf(c_0_69, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_64, c_0_59])).
% 0.21/0.39  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_41]), c_0_62]), c_0_43])])).
% 0.21/0.39  cnf(c_0_71, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_72, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_67])).
% 0.21/0.39  cnf(c_0_73, plain, (r1_tarski(k1_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.21/0.39  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_70, c_0_39])).
% 0.21/0.39  cnf(c_0_75, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_71]), c_0_72])).
% 0.21/0.39  cnf(c_0_76, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_30, c_0_72])).
% 0.21/0.39  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_72])).
% 0.21/0.39  cnf(c_0_78, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_62])).
% 0.21/0.39  cnf(c_0_79, negated_conjecture, (r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_43]), c_0_41])])).
% 0.21/0.39  cnf(c_0_80, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relat_1(X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.21/0.39  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_49]), c_0_41]), c_0_43])])).
% 0.21/0.39  cnf(c_0_82, negated_conjecture, (~v1_funct_2(esk6_0,esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_56, c_0_61])).
% 0.21/0.39  cnf(c_0_83, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.39  cnf(c_0_84, negated_conjecture, (v1_funct_2(esk6_0,k1_xboole_0,X1)|~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_43]), c_0_78])).
% 0.21/0.39  cnf(c_0_85, negated_conjecture, (~v1_funct_2(esk6_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.21/0.39  cnf(c_0_86, negated_conjecture, (v1_funct_2(esk6_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_79])])).
% 0.21/0.39  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 88
% 0.21/0.39  # Proof object clause steps            : 67
% 0.21/0.39  # Proof object formula steps           : 21
% 0.21/0.39  # Proof object conjectures             : 31
% 0.21/0.39  # Proof object clause conjectures      : 28
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 18
% 0.21/0.39  # Proof object initial formulas used   : 10
% 0.21/0.39  # Proof object generating inferences   : 31
% 0.21/0.39  # Proof object simplifying inferences  : 48
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 10
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 33
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 33
% 0.21/0.39  # Processed clauses                    : 174
% 0.21/0.39  # ...of these trivial                  : 3
% 0.21/0.39  # ...subsumed                          : 21
% 0.21/0.39  # ...remaining for further processing  : 150
% 0.21/0.39  # Other redundant clauses eliminated   : 19
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 4
% 0.21/0.39  # Backward-rewritten                   : 36
% 0.21/0.39  # Generated clauses                    : 193
% 0.21/0.39  # ...of the previous two non-trivial   : 188
% 0.21/0.39  # Contextual simplify-reflections      : 3
% 0.21/0.39  # Paramodulations                      : 177
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 19
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 63
% 0.21/0.39  #    Positive orientable unit clauses  : 13
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 0
% 0.21/0.39  #    Non-unit-clauses                  : 50
% 0.21/0.39  # Current number of unprocessed clauses: 72
% 0.21/0.39  # ...number of literals in the above   : 265
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 72
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 1076
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 478
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 27
% 0.21/0.39  # Unit Clause-clause subsumption calls : 374
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 15
% 0.21/0.39  # BW rewrite match successes           : 12
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 5390
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.037 s
% 0.21/0.39  # System time              : 0.005 s
% 0.21/0.39  # Total time               : 0.042 s
% 0.21/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
