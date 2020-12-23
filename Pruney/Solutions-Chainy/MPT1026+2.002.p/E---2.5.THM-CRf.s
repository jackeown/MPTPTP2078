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

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 545 expanded)
%              Number of clauses        :   63 ( 277 expanded)
%              Number of leaves         :   13 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          :  368 (4318 expanded)
%              Number of equality atoms :   57 (1578 expanded)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

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

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

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

fof(c_0_13,plain,(
    ! [X36,X37,X38,X39,X41,X42,X43,X44,X45,X47] :
      ( ( v1_relat_1(esk3_4(X36,X37,X38,X39))
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( v1_funct_1(esk3_4(X36,X37,X38,X39))
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( X39 = esk3_4(X36,X37,X38,X39)
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( k1_relat_1(esk3_4(X36,X37,X38,X39)) = X36
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( r1_tarski(k2_relat_1(esk3_4(X36,X37,X38,X39)),X37)
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42)
        | X41 != X42
        | k1_relat_1(X42) != X36
        | ~ r1_tarski(k2_relat_1(X42),X37)
        | r2_hidden(X41,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( ~ r2_hidden(esk4_3(X43,X44,X45),X45)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47)
        | esk4_3(X43,X44,X45) != X47
        | k1_relat_1(X47) != X43
        | ~ r1_tarski(k2_relat_1(X47),X44)
        | X45 = k1_funct_2(X43,X44) )
      & ( v1_relat_1(esk5_3(X43,X44,X45))
        | r2_hidden(esk4_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) )
      & ( v1_funct_1(esk5_3(X43,X44,X45))
        | r2_hidden(esk4_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) )
      & ( esk4_3(X43,X44,X45) = esk5_3(X43,X44,X45)
        | r2_hidden(esk4_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) )
      & ( k1_relat_1(esk5_3(X43,X44,X45)) = X43
        | r2_hidden(esk4_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) )
      & ( r1_tarski(k2_relat_1(esk5_3(X43,X44,X45)),X44)
        | r2_hidden(esk4_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_14,plain,
    ( k1_relat_1(esk3_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_15,plain,
    ( X1 = esk3_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_17,plain,
    ( v1_relat_1(esk3_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_funct_1(esk3_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_20,plain,(
    ! [X49] :
      ( ( v1_funct_1(X49)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) )
      & ( v1_funct_2(X49,k1_relat_1(X49),k2_relat_1(X49))
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) )
      & ( m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X49),k2_relat_1(X49))))
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( esk3_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_23,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))
    & ( ~ v1_funct_1(esk9_0)
      | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
      | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v1_funct_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_31,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

fof(c_0_32,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

fof(c_0_37,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_xboole_0(X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X24)))
      | v1_xboole_0(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_38,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_39,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_44])).

fof(c_0_49,plain,(
    ! [X21,X22,X23] :
      ( ( X23 != k1_funct_1(X21,X22)
        | r2_hidden(k4_tarski(X22,X23),X21)
        | ~ r2_hidden(X22,k1_relat_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X22,X23),X21)
        | X23 = k1_funct_1(X21,X22)
        | ~ r2_hidden(X22,k1_relat_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( X23 != k1_funct_1(X21,X22)
        | X23 = k1_xboole_0
        | r2_hidden(X22,k1_relat_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( X23 != k1_xboole_0
        | X23 = k1_funct_1(X21,X22)
        | r2_hidden(X22,k1_relat_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_50,plain,(
    ! [X50,X51,X52] :
      ( ( v1_funct_1(X52)
        | r2_hidden(esk6_3(X50,X51,X52),X50)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_2(X52,X50,X51)
        | r2_hidden(esk6_3(X50,X51,X52),X50)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | r2_hidden(esk6_3(X50,X51,X52),X50)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_1(X52)
        | ~ r2_hidden(k1_funct_1(X52,esk6_3(X50,X51,X52)),X51)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_2(X52,X50,X51)
        | ~ r2_hidden(k1_funct_1(X52,esk6_3(X50,X51,X52)),X51)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | ~ r2_hidden(k1_funct_1(X52,esk6_3(X50,X51,X52)),X51)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_funct_1(esk9_0)
    | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_52,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(k1_relat_1(X29),X27)
      | ~ r1_tarski(k2_relat_1(X29),X28)
      | m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk6_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_36])])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_relat_1(esk3_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ v1_funct_1(esk9_0)
    | ~ r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_43])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_63,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | r2_hidden(esk6_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ v1_relat_1(esk9_0)
    | ~ r1_tarski(k1_relat_1(esk9_0),esk7_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( r1_tarski(k2_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

fof(c_0_67,plain,(
    ! [X33,X34,X35] :
      ( ( v1_funct_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | v1_xboole_0(X34) )
      & ( v1_partfun1(X35,X33)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_68,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_36])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk9_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_63]),c_0_35]),c_0_36]),c_0_34])])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,X1)
    | r2_hidden(esk6_3(esk7_0,X1,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_35]),c_0_34]),c_0_34]),c_0_34]),c_0_36])])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ r1_tarski(k1_relat_1(esk9_0),esk7_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_35])])).

cnf(c_0_74,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_22])).

fof(c_0_75,plain,(
    ! [X30,X31,X32] :
      ( ( v1_funct_1(X32)
        | ~ v1_funct_1(X32)
        | ~ v1_partfun1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_funct_2(X32,X30,X31)
        | ~ v1_funct_1(X32)
        | ~ v1_partfun1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_76,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_34]),c_0_48])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_29])).

cnf(c_0_83,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( v1_partfun1(esk9_0,esk7_0)
    | v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_36])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_87,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_83,c_0_58])).

cnf(c_0_88,negated_conjecture,
    ( v1_partfun1(esk9_0,esk7_0) ),
    inference(sr,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_35]),c_0_36]),c_0_34]),c_0_48]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.029 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.20/0.41  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.41  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.41  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.20/0.41  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 0.20/0.41  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.20/0.41  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.41  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.20/0.41  fof(c_0_13, plain, ![X36, X37, X38, X39, X41, X42, X43, X44, X45, X47]:(((((((v1_relat_1(esk3_4(X36,X37,X38,X39))|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37))&(v1_funct_1(esk3_4(X36,X37,X38,X39))|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37)))&(X39=esk3_4(X36,X37,X38,X39)|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37)))&(k1_relat_1(esk3_4(X36,X37,X38,X39))=X36|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37)))&(r1_tarski(k2_relat_1(esk3_4(X36,X37,X38,X39)),X37)|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37)))&(~v1_relat_1(X42)|~v1_funct_1(X42)|X41!=X42|k1_relat_1(X42)!=X36|~r1_tarski(k2_relat_1(X42),X37)|r2_hidden(X41,X38)|X38!=k1_funct_2(X36,X37)))&((~r2_hidden(esk4_3(X43,X44,X45),X45)|(~v1_relat_1(X47)|~v1_funct_1(X47)|esk4_3(X43,X44,X45)!=X47|k1_relat_1(X47)!=X43|~r1_tarski(k2_relat_1(X47),X44))|X45=k1_funct_2(X43,X44))&(((((v1_relat_1(esk5_3(X43,X44,X45))|r2_hidden(esk4_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44))&(v1_funct_1(esk5_3(X43,X44,X45))|r2_hidden(esk4_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44)))&(esk4_3(X43,X44,X45)=esk5_3(X43,X44,X45)|r2_hidden(esk4_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44)))&(k1_relat_1(esk5_3(X43,X44,X45))=X43|r2_hidden(esk4_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44)))&(r1_tarski(k2_relat_1(esk5_3(X43,X44,X45)),X44)|r2_hidden(esk4_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.20/0.41  cnf(c_0_14, plain, (k1_relat_1(esk3_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_15, plain, (X1=esk3_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.20/0.41  cnf(c_0_17, plain, (v1_relat_1(esk3_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_18, plain, (v1_funct_1(esk3_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  fof(c_0_19, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  fof(c_0_20, plain, ![X49]:(((v1_funct_1(X49)|(~v1_relat_1(X49)|~v1_funct_1(X49)))&(v1_funct_2(X49,k1_relat_1(X49),k2_relat_1(X49))|(~v1_relat_1(X49)|~v1_funct_1(X49))))&(m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X49),k2_relat_1(X49))))|(~v1_relat_1(X49)|~v1_funct_1(X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.41  cnf(c_0_21, plain, (k1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_22, plain, (esk3_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.41  fof(c_0_23, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))&(~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.41  cnf(c_0_24, plain, (v1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_25, plain, (v1_funct_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_28, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_30, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.20/0.41  cnf(c_0_31, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.20/0.41  fof(c_0_32, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.41  cnf(c_0_33, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk9_0)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.20/0.41  fof(c_0_37, plain, ![X24, X25, X26]:(~v1_xboole_0(X24)|(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X24)))|v1_xboole_0(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.20/0.41  fof(c_0_38, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  fof(c_0_39, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.41  cnf(c_0_40, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.41  cnf(c_0_42, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_44, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_45, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_47, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.41  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_44])).
% 0.20/0.41  fof(c_0_49, plain, ![X21, X22, X23]:(((X23!=k1_funct_1(X21,X22)|r2_hidden(k4_tarski(X22,X23),X21)|~r2_hidden(X22,k1_relat_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(~r2_hidden(k4_tarski(X22,X23),X21)|X23=k1_funct_1(X21,X22)|~r2_hidden(X22,k1_relat_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21))))&((X23!=k1_funct_1(X21,X22)|X23=k1_xboole_0|r2_hidden(X22,k1_relat_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(X23!=k1_xboole_0|X23=k1_funct_1(X21,X22)|r2_hidden(X22,k1_relat_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.20/0.41  fof(c_0_50, plain, ![X50, X51, X52]:((((v1_funct_1(X52)|(r2_hidden(esk6_3(X50,X51,X52),X50)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(v1_funct_2(X52,X50,X51)|(r2_hidden(esk6_3(X50,X51,X52),X50)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|(r2_hidden(esk6_3(X50,X51,X52),X50)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(((v1_funct_1(X52)|(~r2_hidden(k1_funct_1(X52,esk6_3(X50,X51,X52)),X51)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(v1_funct_2(X52,X50,X51)|(~r2_hidden(k1_funct_1(X52,esk6_3(X50,X51,X52)),X51)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|(~r2_hidden(k1_funct_1(X52,esk6_3(X50,X51,X52)),X51)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  fof(c_0_52, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(k1_relat_1(X29),X27)|~r1_tarski(k2_relat_1(X29),X28)|m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (~r2_hidden(X1,esk9_0)|~v1_xboole_0(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.41  cnf(c_0_54, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.41  cnf(c_0_55, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_56, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk6_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_36])])).
% 0.20/0.41  cnf(c_0_58, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.41  cnf(c_0_59, plain, (r1_tarski(k2_relat_1(esk3_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~v1_funct_1(esk9_0)|~r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_43])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,esk9_0)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.41  cnf(c_0_62, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  cnf(c_0_63, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_55])).
% 0.20/0.41  cnf(c_0_64, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|r2_hidden(esk6_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(er,[status(thm)],[c_0_56])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~v1_relat_1(esk9_0)|~r1_tarski(k1_relat_1(esk9_0),esk7_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.41  cnf(c_0_66, plain, (r1_tarski(k2_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_59])).
% 0.20/0.41  fof(c_0_67, plain, ![X33, X34, X35]:((v1_funct_1(X35)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_xboole_0(X34))&(v1_partfun1(X35,X33)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_xboole_0(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.41  cnf(c_0_68, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_36])])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (r1_tarski(esk9_0,X1)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,esk7_0)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_63]), c_0_35]), c_0_36]), c_0_34])])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,X1)|r2_hidden(esk6_3(esk7_0,X1,esk9_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_35]), c_0_34]), c_0_34]), c_0_34]), c_0_36])])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~r1_tarski(k1_relat_1(esk9_0),esk7_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_35])])).
% 0.20/0.41  cnf(c_0_74, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_66, c_0_22])).
% 0.20/0.41  fof(c_0_75, plain, ![X30, X31, X32]:((v1_funct_1(X32)|(~v1_funct_1(X32)|~v1_partfun1(X32,X30))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v1_funct_2(X32,X30,X31)|(~v1_funct_1(X32)|~v1_partfun1(X32,X30))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.20/0.41  cnf(c_0_76, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,X1)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_34]), c_0_48])])).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_74, c_0_29])).
% 0.20/0.41  cnf(c_0_83, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (v1_partfun1(esk9_0,esk7_0)|v1_xboole_0(k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_36])])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.20/0.41  cnf(c_0_87, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_83, c_0_58])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (v1_partfun1(esk9_0,esk7_0)), inference(sr,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_35]), c_0_36]), c_0_34]), c_0_48]), c_0_82])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 90
% 0.20/0.41  # Proof object clause steps            : 63
% 0.20/0.41  # Proof object formula steps           : 27
% 0.20/0.41  # Proof object conjectures             : 31
% 0.20/0.41  # Proof object clause conjectures      : 28
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 21
% 0.20/0.41  # Proof object initial formulas used   : 13
% 0.20/0.41  # Proof object generating inferences   : 28
% 0.20/0.41  # Proof object simplifying inferences  : 48
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 14
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 44
% 0.20/0.41  # Removed in clause preprocessing      : 5
% 0.20/0.41  # Initial clauses in saturation        : 39
% 0.20/0.41  # Processed clauses                    : 556
% 0.20/0.41  # ...of these trivial                  : 4
% 0.20/0.41  # ...subsumed                          : 295
% 0.20/0.41  # ...remaining for further processing  : 257
% 0.20/0.41  # Other redundant clauses eliminated   : 18
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 9
% 0.20/0.41  # Backward-rewritten                   : 16
% 0.20/0.41  # Generated clauses                    : 809
% 0.20/0.41  # ...of the previous two non-trivial   : 772
% 0.20/0.41  # Contextual simplify-reflections      : 8
% 0.20/0.41  # Paramodulations                      : 792
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 18
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 178
% 0.20/0.41  #    Positive orientable unit clauses  : 11
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 7
% 0.20/0.41  #    Non-unit-clauses                  : 160
% 0.20/0.41  # Current number of unprocessed clauses: 276
% 0.20/0.41  # ...number of literals in the above   : 1300
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 63
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 6781
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 2527
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 160
% 0.20/0.41  # Unit Clause-clause subsumption calls : 298
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 9
% 0.20/0.41  # BW rewrite match successes           : 5
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 15012
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.058 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.063 s
% 0.20/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
