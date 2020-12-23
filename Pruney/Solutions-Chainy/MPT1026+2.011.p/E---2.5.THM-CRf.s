%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 546 expanded)
%              Number of clauses        :   66 ( 277 expanded)
%              Number of leaves         :   15 ( 119 expanded)
%              Depth                    :   17
%              Number of atoms          :  362 (4205 expanded)
%              Number of equality atoms :   47 (1518 expanded)
%              Maximal formula depth    :   25 (   5 average)
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

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t5_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

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

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(c_0_15,plain,(
    ! [X42,X43,X44,X45,X47,X48,X49,X50,X51,X53] :
      ( ( v1_relat_1(esk3_4(X42,X43,X44,X45))
        | ~ r2_hidden(X45,X44)
        | X44 != k1_funct_2(X42,X43) )
      & ( v1_funct_1(esk3_4(X42,X43,X44,X45))
        | ~ r2_hidden(X45,X44)
        | X44 != k1_funct_2(X42,X43) )
      & ( X45 = esk3_4(X42,X43,X44,X45)
        | ~ r2_hidden(X45,X44)
        | X44 != k1_funct_2(X42,X43) )
      & ( k1_relat_1(esk3_4(X42,X43,X44,X45)) = X42
        | ~ r2_hidden(X45,X44)
        | X44 != k1_funct_2(X42,X43) )
      & ( r1_tarski(k2_relat_1(esk3_4(X42,X43,X44,X45)),X43)
        | ~ r2_hidden(X45,X44)
        | X44 != k1_funct_2(X42,X43) )
      & ( ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48)
        | X47 != X48
        | k1_relat_1(X48) != X42
        | ~ r1_tarski(k2_relat_1(X48),X43)
        | r2_hidden(X47,X44)
        | X44 != k1_funct_2(X42,X43) )
      & ( ~ r2_hidden(esk4_3(X49,X50,X51),X51)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53)
        | esk4_3(X49,X50,X51) != X53
        | k1_relat_1(X53) != X49
        | ~ r1_tarski(k2_relat_1(X53),X50)
        | X51 = k1_funct_2(X49,X50) )
      & ( v1_relat_1(esk5_3(X49,X50,X51))
        | r2_hidden(esk4_3(X49,X50,X51),X51)
        | X51 = k1_funct_2(X49,X50) )
      & ( v1_funct_1(esk5_3(X49,X50,X51))
        | r2_hidden(esk4_3(X49,X50,X51),X51)
        | X51 = k1_funct_2(X49,X50) )
      & ( esk4_3(X49,X50,X51) = esk5_3(X49,X50,X51)
        | r2_hidden(esk4_3(X49,X50,X51),X51)
        | X51 = k1_funct_2(X49,X50) )
      & ( k1_relat_1(esk5_3(X49,X50,X51)) = X49
        | r2_hidden(esk4_3(X49,X50,X51),X51)
        | X51 = k1_funct_2(X49,X50) )
      & ( r1_tarski(k2_relat_1(esk5_3(X49,X50,X51)),X50)
        | r2_hidden(esk4_3(X49,X50,X51),X51)
        | X51 = k1_funct_2(X49,X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_16,plain,
    ( k1_relat_1(esk3_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_17,plain,
    ( X1 = esk3_4(X2,X3,X4,X1)
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
    ( v1_funct_1(esk3_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(esk3_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( esk3_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_23,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))
    & ( ~ v1_funct_1(esk9_0)
      | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
      | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( v1_funct_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( v1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X55] :
      ( ( v1_funct_1(X55)
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55) )
      & ( v1_funct_2(X55,k1_relat_1(X55),k2_relat_1(X55))
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55) )
      & ( m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X55),k2_relat_1(X55))))
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_27,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

fof(c_0_31,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

fof(c_0_36,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

fof(c_0_39,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_xboole_0(X30)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))
      | v1_xboole_0(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_40,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_41,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_42,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_46])).

fof(c_0_51,plain,(
    ! [X56,X57,X58] :
      ( ( v1_funct_1(X58)
        | r2_hidden(esk6_3(X56,X57,X58),X56)
        | k1_relat_1(X58) != X56
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( v1_funct_2(X58,X56,X57)
        | r2_hidden(esk6_3(X56,X57,X58),X56)
        | k1_relat_1(X58) != X56
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | r2_hidden(esk6_3(X56,X57,X58),X56)
        | k1_relat_1(X58) != X56
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( v1_funct_1(X58)
        | ~ r2_hidden(k1_funct_1(X58,esk6_3(X56,X57,X58)),X57)
        | k1_relat_1(X58) != X56
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( v1_funct_2(X58,X56,X57)
        | ~ r2_hidden(k1_funct_1(X58,esk6_3(X56,X57,X58)),X57)
        | k1_relat_1(X58) != X56
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ r2_hidden(k1_funct_1(X58,esk6_3(X56,X57,X58)),X57)
        | k1_relat_1(X58) != X56
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

fof(c_0_52,plain,(
    ! [X27,X28,X29] :
      ( ( v4_relat_1(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( v5_relat_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk6_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_56,plain,(
    ! [X20,X21] :
      ( ( ~ v4_relat_1(X21,X20)
        | r1_tarski(k1_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_tarski(k1_relat_1(X21),X20)
        | v4_relat_1(X21,X20)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_57,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_60,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ r1_tarski(k1_relat_1(X35),X33)
      | ~ r1_tarski(k2_relat_1(X35),X34)
      | m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_1(esk9_0)
    | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_62,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | ~ r1_tarski(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_63,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | r2_hidden(esk6_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_45])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk9_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( r1_tarski(k2_relat_1(esk3_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ v1_funct_1(esk9_0)
    | ~ r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_45])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,X1)
    | r2_hidden(esk6_3(esk7_0,X1,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_34]),c_0_33]),c_0_33]),c_0_33]),c_0_35])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | ~ v4_relat_1(esk9_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_33]),c_0_35])])).

cnf(c_0_73,negated_conjecture,
    ( v4_relat_1(esk9_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ v1_funct_1(esk9_0)
    | ~ v1_relat_1(esk9_0)
    | ~ r1_tarski(k1_relat_1(esk9_0),esk7_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_67])).

cnf(c_0_75,plain,
    ( r1_tarski(k2_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_68])).

fof(c_0_76,plain,(
    ! [X39,X40,X41] :
      ( ( v1_funct_1(X41)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | v1_xboole_0(X40) )
      & ( v1_partfun1(X41,X39)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_77,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_34])])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,X1)
    | ~ r1_tarski(esk7_0,esk6_3(esk7_0,X1,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ r1_tarski(k1_relat_1(esk9_0),esk7_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_34])]),c_0_35])])).

cnf(c_0_82,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_22])).

fof(c_0_83,plain,(
    ! [X36,X37,X38] :
      ( ( v1_funct_1(X38)
        | ~ v1_funct_1(X38)
        | ~ v1_partfun1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v1_funct_2(X38,X36,X37)
        | ~ v1_funct_1(X38)
        | ~ v1_partfun1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_84,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_66])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_33]),c_0_50])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_28])).

cnf(c_0_90,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( v1_partfun1(esk9_0,esk7_0)
    | v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_38]),c_0_85]),c_0_34])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])])).

cnf(c_0_94,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_90,c_0_67])).

cnf(c_0_95,negated_conjecture,
    ( v1_partfun1(esk9_0,esk7_0) ),
    inference(sr,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_34]),c_0_35]),c_0_33]),c_0_50]),c_0_89])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:03:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
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
% 0.19/0.42  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.42  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.19/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.42  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 0.19/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.42  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.42  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.42  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.42  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.42  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.19/0.42  fof(c_0_15, plain, ![X42, X43, X44, X45, X47, X48, X49, X50, X51, X53]:(((((((v1_relat_1(esk3_4(X42,X43,X44,X45))|~r2_hidden(X45,X44)|X44!=k1_funct_2(X42,X43))&(v1_funct_1(esk3_4(X42,X43,X44,X45))|~r2_hidden(X45,X44)|X44!=k1_funct_2(X42,X43)))&(X45=esk3_4(X42,X43,X44,X45)|~r2_hidden(X45,X44)|X44!=k1_funct_2(X42,X43)))&(k1_relat_1(esk3_4(X42,X43,X44,X45))=X42|~r2_hidden(X45,X44)|X44!=k1_funct_2(X42,X43)))&(r1_tarski(k2_relat_1(esk3_4(X42,X43,X44,X45)),X43)|~r2_hidden(X45,X44)|X44!=k1_funct_2(X42,X43)))&(~v1_relat_1(X48)|~v1_funct_1(X48)|X47!=X48|k1_relat_1(X48)!=X42|~r1_tarski(k2_relat_1(X48),X43)|r2_hidden(X47,X44)|X44!=k1_funct_2(X42,X43)))&((~r2_hidden(esk4_3(X49,X50,X51),X51)|(~v1_relat_1(X53)|~v1_funct_1(X53)|esk4_3(X49,X50,X51)!=X53|k1_relat_1(X53)!=X49|~r1_tarski(k2_relat_1(X53),X50))|X51=k1_funct_2(X49,X50))&(((((v1_relat_1(esk5_3(X49,X50,X51))|r2_hidden(esk4_3(X49,X50,X51),X51)|X51=k1_funct_2(X49,X50))&(v1_funct_1(esk5_3(X49,X50,X51))|r2_hidden(esk4_3(X49,X50,X51),X51)|X51=k1_funct_2(X49,X50)))&(esk4_3(X49,X50,X51)=esk5_3(X49,X50,X51)|r2_hidden(esk4_3(X49,X50,X51),X51)|X51=k1_funct_2(X49,X50)))&(k1_relat_1(esk5_3(X49,X50,X51))=X49|r2_hidden(esk4_3(X49,X50,X51),X51)|X51=k1_funct_2(X49,X50)))&(r1_tarski(k2_relat_1(esk5_3(X49,X50,X51)),X50)|r2_hidden(esk4_3(X49,X50,X51),X51)|X51=k1_funct_2(X49,X50))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.19/0.42  cnf(c_0_16, plain, (k1_relat_1(esk3_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_17, plain, (X1=esk3_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.19/0.42  cnf(c_0_19, plain, (v1_funct_1(esk3_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_20, plain, (v1_relat_1(esk3_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_21, plain, (k1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_22, plain, (esk3_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.42  fof(c_0_23, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))&(~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.42  cnf(c_0_24, plain, (v1_funct_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_25, plain, (v1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.42  fof(c_0_26, plain, ![X55]:(((v1_funct_1(X55)|(~v1_relat_1(X55)|~v1_funct_1(X55)))&(v1_funct_2(X55,k1_relat_1(X55),k2_relat_1(X55))|(~v1_relat_1(X55)|~v1_funct_1(X55))))&(m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X55),k2_relat_1(X55))))|(~v1_relat_1(X55)|~v1_funct_1(X55)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.42  cnf(c_0_27, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.42  cnf(c_0_28, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_29, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.19/0.42  cnf(c_0_30, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.19/0.42  fof(c_0_31, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk9_0)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.19/0.42  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.19/0.42  fof(c_0_36, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.42  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.19/0.42  fof(c_0_39, plain, ![X30, X31, X32]:(~v1_xboole_0(X30)|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))|v1_xboole_0(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.19/0.42  fof(c_0_40, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  fof(c_0_41, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_42, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.42  cnf(c_0_44, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.42  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  cnf(c_0_46, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.42  cnf(c_0_47, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.42  cnf(c_0_49, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.42  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.42  fof(c_0_51, plain, ![X56, X57, X58]:((((v1_funct_1(X58)|(r2_hidden(esk6_3(X56,X57,X58),X56)|k1_relat_1(X58)!=X56)|(~v1_relat_1(X58)|~v1_funct_1(X58)))&(v1_funct_2(X58,X56,X57)|(r2_hidden(esk6_3(X56,X57,X58),X56)|k1_relat_1(X58)!=X56)|(~v1_relat_1(X58)|~v1_funct_1(X58))))&(m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|(r2_hidden(esk6_3(X56,X57,X58),X56)|k1_relat_1(X58)!=X56)|(~v1_relat_1(X58)|~v1_funct_1(X58))))&(((v1_funct_1(X58)|(~r2_hidden(k1_funct_1(X58,esk6_3(X56,X57,X58)),X57)|k1_relat_1(X58)!=X56)|(~v1_relat_1(X58)|~v1_funct_1(X58)))&(v1_funct_2(X58,X56,X57)|(~r2_hidden(k1_funct_1(X58,esk6_3(X56,X57,X58)),X57)|k1_relat_1(X58)!=X56)|(~v1_relat_1(X58)|~v1_funct_1(X58))))&(m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|(~r2_hidden(k1_funct_1(X58,esk6_3(X56,X57,X58)),X57)|k1_relat_1(X58)!=X56)|(~v1_relat_1(X58)|~v1_funct_1(X58))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.19/0.42  fof(c_0_52, plain, ![X27, X28, X29]:((v4_relat_1(X29,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(v5_relat_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (~r2_hidden(X1,esk9_0)|~v1_xboole_0(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.42  cnf(c_0_54, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.42  cnf(c_0_55, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk6_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  fof(c_0_56, plain, ![X20, X21]:((~v4_relat_1(X21,X20)|r1_tarski(k1_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_tarski(k1_relat_1(X21),X20)|v4_relat_1(X21,X20)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.42  cnf(c_0_57, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, (~r2_hidden(X1,esk9_0)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.42  cnf(c_0_59, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  fof(c_0_60, plain, ![X33, X34, X35]:(~v1_relat_1(X35)|(~r1_tarski(k1_relat_1(X35),X33)|~r1_tarski(k2_relat_1(X35),X34)|m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  fof(c_0_62, plain, ![X22, X23]:(~r2_hidden(X22,X23)|~r1_tarski(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.42  cnf(c_0_63, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|r2_hidden(esk6_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.42  cnf(c_0_64, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.42  cnf(c_0_65, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_57, c_0_45])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (r1_tarski(esk9_0,X1)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.42  cnf(c_0_67, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.42  cnf(c_0_68, plain, (r1_tarski(k2_relat_1(esk3_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~v1_funct_1(esk9_0)|~r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_61, c_0_45])).
% 0.19/0.42  cnf(c_0_70, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,X1)|r2_hidden(esk6_3(esk7_0,X1,esk9_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_34]), c_0_33]), c_0_33]), c_0_33]), c_0_35])])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (r1_tarski(esk7_0,X1)|~v4_relat_1(esk9_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_33]), c_0_35])])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (v4_relat_1(esk9_0,X1)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~v1_funct_1(esk9_0)|~v1_relat_1(esk9_0)|~r1_tarski(k1_relat_1(esk9_0),esk7_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_61, c_0_67])).
% 0.19/0.42  cnf(c_0_75, plain, (r1_tarski(k2_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_68])).
% 0.19/0.42  fof(c_0_76, plain, ![X39, X40, X41]:((v1_funct_1(X41)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_xboole_0(X40))&(v1_partfun1(X41,X39)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_xboole_0(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.42  cnf(c_0_77, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_34])])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,X1)|~r1_tarski(esk7_0,esk6_3(esk7_0,X1,esk9_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (r1_tarski(esk7_0,X1)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~r1_tarski(k1_relat_1(esk9_0),esk7_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_34])]), c_0_35])])).
% 0.19/0.42  cnf(c_0_82, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_75, c_0_22])).
% 0.19/0.42  fof(c_0_83, plain, ![X36, X37, X38]:((v1_funct_1(X38)|(~v1_funct_1(X38)|~v1_partfun1(X38,X36))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(v1_funct_2(X38,X36,X37)|(~v1_funct_1(X38)|~v1_partfun1(X38,X36))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.19/0.42  cnf(c_0_84, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.42  cnf(c_0_85, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_33]), c_0_34]), c_0_35])])).
% 0.19/0.42  cnf(c_0_86, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_78, c_0_66])).
% 0.19/0.42  cnf(c_0_87, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,X1)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.42  cnf(c_0_88, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_33]), c_0_50])])).
% 0.19/0.42  cnf(c_0_89, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_82, c_0_28])).
% 0.19/0.42  cnf(c_0_90, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.42  cnf(c_0_91, negated_conjecture, (v1_partfun1(esk9_0,esk7_0)|v1_xboole_0(k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_38]), c_0_85]), c_0_34])])).
% 0.19/0.42  cnf(c_0_92, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.42  cnf(c_0_93, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89])])).
% 0.19/0.42  cnf(c_0_94, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_90, c_0_67])).
% 0.19/0.42  cnf(c_0_95, negated_conjecture, (v1_partfun1(esk9_0,esk7_0)), inference(sr,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.42  cnf(c_0_96, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_34]), c_0_35]), c_0_33]), c_0_50]), c_0_89])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 97
% 0.19/0.42  # Proof object clause steps            : 66
% 0.19/0.42  # Proof object formula steps           : 31
% 0.19/0.42  # Proof object conjectures             : 33
% 0.19/0.42  # Proof object clause conjectures      : 30
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 23
% 0.19/0.42  # Proof object initial formulas used   : 15
% 0.19/0.42  # Proof object generating inferences   : 31
% 0.19/0.42  # Proof object simplifying inferences  : 42
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 16
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 45
% 0.19/0.42  # Removed in clause preprocessing      : 5
% 0.19/0.42  # Initial clauses in saturation        : 40
% 0.19/0.42  # Processed clauses                    : 996
% 0.19/0.42  # ...of these trivial                  : 1
% 0.19/0.42  # ...subsumed                          : 643
% 0.19/0.42  # ...remaining for further processing  : 352
% 0.19/0.42  # Other redundant clauses eliminated   : 15
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 12
% 0.19/0.42  # Backward-rewritten                   : 11
% 0.19/0.42  # Generated clauses                    : 1693
% 0.19/0.42  # ...of the previous two non-trivial   : 1583
% 0.19/0.42  # Contextual simplify-reflections      : 16
% 0.19/0.42  # Paramodulations                      : 1679
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 15
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
% 0.19/0.42  # Current number of processed clauses  : 276
% 0.19/0.42  #    Positive orientable unit clauses  : 20
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 10
% 0.19/0.42  #    Non-unit-clauses                  : 246
% 0.19/0.42  # Current number of unprocessed clauses: 651
% 0.19/0.42  # ...number of literals in the above   : 2887
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 63
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 20140
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 10122
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 347
% 0.19/0.42  # Unit Clause-clause subsumption calls : 710
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 10
% 0.19/0.42  # BW rewrite match successes           : 4
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 23978
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.077 s
% 0.19/0.42  # System time              : 0.007 s
% 0.19/0.42  # Total time               : 0.084 s
% 0.19/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
