%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 724 expanded)
%              Number of clauses        :   80 ( 368 expanded)
%              Number of leaves         :   15 ( 160 expanded)
%              Depth                    :   15
%              Number of atoms          :  370 (5177 expanded)
%              Number of equality atoms :   48 (1798 expanded)
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

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(c_0_15,plain,(
    ! [X43,X44,X45,X46,X48,X49,X50,X51,X52,X54] :
      ( ( v1_relat_1(esk2_4(X43,X44,X45,X46))
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( v1_funct_1(esk2_4(X43,X44,X45,X46))
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( X46 = esk2_4(X43,X44,X45,X46)
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( k1_relat_1(esk2_4(X43,X44,X45,X46)) = X43
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( r1_tarski(k2_relat_1(esk2_4(X43,X44,X45,X46)),X44)
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49)
        | X48 != X49
        | k1_relat_1(X49) != X43
        | ~ r1_tarski(k2_relat_1(X49),X44)
        | r2_hidden(X48,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( ~ r2_hidden(esk3_3(X50,X51,X52),X52)
        | ~ v1_relat_1(X54)
        | ~ v1_funct_1(X54)
        | esk3_3(X50,X51,X52) != X54
        | k1_relat_1(X54) != X50
        | ~ r1_tarski(k2_relat_1(X54),X51)
        | X52 = k1_funct_2(X50,X51) )
      & ( v1_relat_1(esk4_3(X50,X51,X52))
        | r2_hidden(esk3_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) )
      & ( v1_funct_1(esk4_3(X50,X51,X52))
        | r2_hidden(esk3_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) )
      & ( esk3_3(X50,X51,X52) = esk4_3(X50,X51,X52)
        | r2_hidden(esk3_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) )
      & ( k1_relat_1(esk4_3(X50,X51,X52)) = X50
        | r2_hidden(esk3_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) )
      & ( r1_tarski(k2_relat_1(esk4_3(X50,X51,X52)),X51)
        | r2_hidden(esk3_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_16,plain,
    ( k1_relat_1(esk2_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_17,plain,
    ( X1 = esk2_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_19,plain,
    ( v1_funct_1(esk2_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(esk2_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_xboole_0(X22)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X22)))
      | v1_xboole_0(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_22,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_23,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_25,plain,(
    ! [X56] :
      ( ( v1_funct_1(X56)
        | ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56) )
      & ( v1_funct_2(X56,k1_relat_1(X56),k2_relat_1(X56))
        | ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56) )
      & ( m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X56),k2_relat_1(X56))))
        | ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_26,plain,
    ( k1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( esk2_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_28,negated_conjecture,
    ( r2_hidden(esk7_0,k1_funct_2(esk5_0,esk6_0))
    & ( ~ v1_funct_1(esk7_0)
      | ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
      | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_29,plain,
    ( v1_funct_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( v1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk7_0,k1_funct_2(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_51,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k1_relset_1(X28,X29,X30) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_funct_1(esk7_0)
    | ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_54,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_49])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_42])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_59,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_49])).

fof(c_0_61,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k1_relat_1(X33),X31)
      | ~ r1_tarski(k2_relat_1(X33),X32)
      | m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ v1_funct_1(esk7_0)
    | ~ r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_32])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_44])).

fof(c_0_64,plain,(
    ! [X34,X35,X36] :
      ( ( v1_funct_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_partfun1(X36,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v1_funct_2(X36,X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_partfun1(X36,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_67,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | m1_subset_1(k1_relset_1(X25,X26,X27),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_68,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_32])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_44])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ v1_funct_1(esk7_0)
    | ~ v1_relat_1(esk7_0)
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_73,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_xboole_0(X37)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | v1_partfun1(X39,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

fof(c_0_74,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_75,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)) = esk7_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( k1_relset_1(X1,X2,esk7_0) = esk5_0
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_46])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ v1_funct_1(esk7_0)
    | ~ v1_relat_1(esk7_0)
    | ~ r1_tarski(k1_relat_1(esk7_0),esk5_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_70])).

cnf(c_0_79,plain,
    ( r1_tarski(k2_relat_1(esk2_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ v1_relat_1(esk7_0)
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_47])])).

cnf(c_0_81,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_32])).

cnf(c_0_82,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)) = esk7_0
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_49])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k2_relat_1(esk7_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ v1_relat_1(esk7_0)
    | ~ r1_tarski(k1_relat_1(esk7_0),esk5_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_47])])).

cnf(c_0_87,plain,
    ( r1_tarski(k2_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_79])).

fof(c_0_88,plain,(
    ! [X40,X41,X42] :
      ( ( v1_funct_1(X42)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | v1_xboole_0(X41) )
      & ( v1_partfun1(X42,X40)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | v1_xboole_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_89,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_48])])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(esk7_0,X1,X2)
    | ~ v1_partfun1(esk7_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_69]),c_0_47])])).

cnf(c_0_92,plain,
    ( v1_partfun1(X1,X2)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_32])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)))
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_66])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k2_relat_1(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_32]),c_0_69])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ r1_tarski(k1_relat_1(esk7_0),esk5_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_48])])).

cnf(c_0_97,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_27])).

cnf(c_0_98,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_partfun1(esk7_0,esk5_0)
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_101,negated_conjecture,
    ( v1_partfun1(X1,esk5_0)
    | ~ v1_xboole_0(esk5_0)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_46]),c_0_42])])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_38])).

cnf(c_0_105,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0)
    | v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_58]),c_0_99]),c_0_47])])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_42])]),c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_108,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_70])).

cnf(c_0_109,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109]),c_0_47]),c_0_48]),c_0_46]),c_0_42]),c_0_104])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:47:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.029 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.19/0.42  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.19/0.42  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.19/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.42  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.42  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.42  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.42  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.19/0.42  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.19/0.42  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.19/0.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.42  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.42  fof(c_0_15, plain, ![X43, X44, X45, X46, X48, X49, X50, X51, X52, X54]:(((((((v1_relat_1(esk2_4(X43,X44,X45,X46))|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44))&(v1_funct_1(esk2_4(X43,X44,X45,X46))|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44)))&(X46=esk2_4(X43,X44,X45,X46)|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44)))&(k1_relat_1(esk2_4(X43,X44,X45,X46))=X43|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44)))&(r1_tarski(k2_relat_1(esk2_4(X43,X44,X45,X46)),X44)|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44)))&(~v1_relat_1(X49)|~v1_funct_1(X49)|X48!=X49|k1_relat_1(X49)!=X43|~r1_tarski(k2_relat_1(X49),X44)|r2_hidden(X48,X45)|X45!=k1_funct_2(X43,X44)))&((~r2_hidden(esk3_3(X50,X51,X52),X52)|(~v1_relat_1(X54)|~v1_funct_1(X54)|esk3_3(X50,X51,X52)!=X54|k1_relat_1(X54)!=X50|~r1_tarski(k2_relat_1(X54),X51))|X52=k1_funct_2(X50,X51))&(((((v1_relat_1(esk4_3(X50,X51,X52))|r2_hidden(esk3_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51))&(v1_funct_1(esk4_3(X50,X51,X52))|r2_hidden(esk3_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51)))&(esk3_3(X50,X51,X52)=esk4_3(X50,X51,X52)|r2_hidden(esk3_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51)))&(k1_relat_1(esk4_3(X50,X51,X52))=X50|r2_hidden(esk3_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51)))&(r1_tarski(k2_relat_1(esk4_3(X50,X51,X52)),X51)|r2_hidden(esk3_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.19/0.42  cnf(c_0_16, plain, (k1_relat_1(esk2_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_17, plain, (X1=esk2_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.19/0.42  cnf(c_0_19, plain, (v1_funct_1(esk2_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_20, plain, (v1_relat_1(esk2_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  fof(c_0_21, plain, ![X22, X23, X24]:(~v1_xboole_0(X22)|(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X22)))|v1_xboole_0(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.19/0.42  fof(c_0_22, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  fof(c_0_23, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  fof(c_0_24, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|~v1_xboole_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.42  fof(c_0_25, plain, ![X56]:(((v1_funct_1(X56)|(~v1_relat_1(X56)|~v1_funct_1(X56)))&(v1_funct_2(X56,k1_relat_1(X56),k2_relat_1(X56))|(~v1_relat_1(X56)|~v1_funct_1(X56))))&(m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X56),k2_relat_1(X56))))|(~v1_relat_1(X56)|~v1_funct_1(X56)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.42  cnf(c_0_26, plain, (k1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_27, plain, (esk2_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.42  fof(c_0_28, negated_conjecture, (r2_hidden(esk7_0,k1_funct_2(esk5_0,esk6_0))&(~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,esk5_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.42  cnf(c_0_29, plain, (v1_funct_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_30, plain, (v1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_31, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  fof(c_0_35, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.42  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_37, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (r2_hidden(esk7_0,k1_funct_2(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_39, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.19/0.42  cnf(c_0_40, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.19/0.42  cnf(c_0_41, plain, (v1_xboole_0(X1)|~v1_xboole_0(X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.42  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_43, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.19/0.42  cnf(c_0_44, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_45, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (v1_funct_1(esk7_0)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.19/0.42  cnf(c_0_49, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.42  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.42  fof(c_0_51, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k1_relset_1(X28,X29,X30)=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)))|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,esk5_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_54, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_49])).
% 0.19/0.42  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_50, c_0_42])).
% 0.19/0.42  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_46]), c_0_47]), c_0_48])])).
% 0.19/0.42  cnf(c_0_59, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk7_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_52, c_0_49])).
% 0.19/0.42  fof(c_0_61, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k1_relat_1(X33),X31)|~r1_tarski(k2_relat_1(X33),X32)|m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.42  cnf(c_0_62, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~v1_funct_1(esk7_0)|~r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_53, c_0_32])).
% 0.19/0.42  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_44])).
% 0.19/0.42  fof(c_0_64, plain, ![X34, X35, X36]:((v1_funct_1(X36)|(~v1_funct_1(X36)|~v1_partfun1(X36,X34))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(v1_funct_2(X36,X34,X35)|(~v1_funct_1(X36)|~v1_partfun1(X36,X34))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.19/0.42  cnf(c_0_65, plain, (X1=X2|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.42  fof(c_0_67, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|m1_subset_1(k1_relset_1(X25,X26,X27),k1_zfmisc_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.19/0.42  cnf(c_0_68, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_59, c_0_32])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (r1_tarski(esk7_0,X1)|~v1_xboole_0(k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_60, c_0_44])).
% 0.19/0.42  cnf(c_0_70, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~v1_funct_1(esk7_0)|~v1_relat_1(esk7_0)|~v1_xboole_0(k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.42  cnf(c_0_72, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.42  fof(c_0_73, plain, ![X37, X38, X39]:(~v1_xboole_0(X37)|(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|v1_partfun1(X39,X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.19/0.42  fof(c_0_74, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X15,X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0))=esk7_0|~v1_xboole_0(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.42  cnf(c_0_76, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (k1_relset_1(X1,X2,esk7_0)=esk5_0|~v1_xboole_0(k2_relat_1(esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_46])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~v1_funct_1(esk7_0)|~v1_relat_1(esk7_0)|~r1_tarski(k1_relat_1(esk7_0),esk5_0)|~r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_53, c_0_70])).
% 0.19/0.42  cnf(c_0_79, plain, (r1_tarski(k2_relat_1(esk2_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~v1_relat_1(esk7_0)|~v1_xboole_0(k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_47])])).
% 0.19/0.42  cnf(c_0_81, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_72, c_0_32])).
% 0.19/0.42  cnf(c_0_82, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.42  cnf(c_0_83, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.42  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0))=esk7_0|~v1_xboole_0(k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_75, c_0_49])).
% 0.19/0.42  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~v1_xboole_0(k2_relat_1(esk7_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.42  cnf(c_0_86, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~v1_relat_1(esk7_0)|~r1_tarski(k1_relat_1(esk7_0),esk5_0)|~r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_47])])).
% 0.19/0.42  cnf(c_0_87, plain, (r1_tarski(k2_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_79])).
% 0.19/0.42  fof(c_0_88, plain, ![X40, X41, X42]:((v1_funct_1(X42)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_xboole_0(X41))&(v1_partfun1(X42,X40)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_xboole_0(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.42  cnf(c_0_89, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_90, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~v1_xboole_0(k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_48])])).
% 0.19/0.42  cnf(c_0_91, negated_conjecture, (v1_funct_2(esk7_0,X1,X2)|~v1_partfun1(esk7_0,X1)|~v1_xboole_0(k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_69]), c_0_47])])).
% 0.19/0.42  cnf(c_0_92, plain, (v1_partfun1(X1,X2)|~v1_xboole_0(X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_82, c_0_32])).
% 0.19/0.42  cnf(c_0_93, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)))|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_83, c_0_66])).
% 0.19/0.42  cnf(c_0_94, negated_conjecture, (v1_xboole_0(X1)|~v1_xboole_0(k2_relat_1(esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_31, c_0_84])).
% 0.19/0.42  cnf(c_0_95, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~v1_xboole_0(k2_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_32]), c_0_69])).
% 0.19/0.42  cnf(c_0_96, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~r1_tarski(k1_relat_1(esk7_0),esk5_0)|~r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_48])])).
% 0.19/0.42  cnf(c_0_97, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_87, c_0_27])).
% 0.19/0.42  cnf(c_0_98, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.42  cnf(c_0_99, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_46]), c_0_47]), c_0_48])])).
% 0.19/0.42  cnf(c_0_100, negated_conjecture, (~v1_partfun1(esk7_0,esk5_0)|~v1_xboole_0(k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.19/0.42  cnf(c_0_101, negated_conjecture, (v1_partfun1(X1,esk5_0)|~v1_xboole_0(esk5_0)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.42  cnf(c_0_102, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.42  cnf(c_0_103, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_46]), c_0_42])])).
% 0.19/0.42  cnf(c_0_104, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_97, c_0_38])).
% 0.19/0.42  cnf(c_0_105, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)|v1_xboole_0(k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_58]), c_0_99]), c_0_47])])).
% 0.19/0.42  cnf(c_0_106, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_42])]), c_0_102])).
% 0.19/0.42  cnf(c_0_107, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 0.19/0.42  cnf(c_0_108, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_72, c_0_70])).
% 0.19/0.42  cnf(c_0_109, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)), inference(sr,[status(thm)],[c_0_105, c_0_106])).
% 0.19/0.42  cnf(c_0_110, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109]), c_0_47]), c_0_48]), c_0_46]), c_0_42]), c_0_104])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 111
% 0.19/0.42  # Proof object clause steps            : 80
% 0.19/0.42  # Proof object formula steps           : 31
% 0.19/0.42  # Proof object conjectures             : 39
% 0.19/0.42  # Proof object clause conjectures      : 36
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 23
% 0.19/0.42  # Proof object initial formulas used   : 15
% 0.19/0.42  # Proof object generating inferences   : 44
% 0.19/0.42  # Proof object simplifying inferences  : 46
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 15
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 36
% 0.19/0.42  # Removed in clause preprocessing      : 3
% 0.19/0.42  # Initial clauses in saturation        : 33
% 0.19/0.42  # Processed clauses                    : 787
% 0.19/0.42  # ...of these trivial                  : 0
% 0.19/0.42  # ...subsumed                          : 446
% 0.19/0.42  # ...remaining for further processing  : 341
% 0.19/0.42  # Other redundant clauses eliminated   : 11
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 11
% 0.19/0.42  # Backward-rewritten                   : 13
% 0.19/0.42  # Generated clauses                    : 1761
% 0.19/0.42  # ...of the previous two non-trivial   : 1679
% 0.19/0.42  # Contextual simplify-reflections      : 17
% 0.19/0.42  # Paramodulations                      : 1751
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 11
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 275
% 0.19/0.42  #    Positive orientable unit clauses  : 13
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 5
% 0.19/0.42  #    Non-unit-clauses                  : 257
% 0.19/0.42  # Current number of unprocessed clauses: 944
% 0.19/0.42  # ...number of literals in the above   : 4300
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 57
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 14137
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 7417
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 326
% 0.19/0.42  # Unit Clause-clause subsumption calls : 301
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 20
% 0.19/0.42  # BW rewrite match successes           : 5
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 26858
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.083 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.088 s
% 0.19/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
