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

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 502 expanded)
%              Number of clauses        :   60 ( 255 expanded)
%              Number of leaves         :   11 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  339 (4112 expanded)
%              Number of equality atoms :   56 (1532 expanded)
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

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

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

fof(c_0_11,plain,(
    ! [X43,X44,X45,X46,X48,X49,X50,X51,X52,X54] :
      ( ( v1_relat_1(esk8_4(X43,X44,X45,X46))
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( v1_funct_1(esk8_4(X43,X44,X45,X46))
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( X46 = esk8_4(X43,X44,X45,X46)
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( k1_relat_1(esk8_4(X43,X44,X45,X46)) = X43
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( r1_tarski(k2_relat_1(esk8_4(X43,X44,X45,X46)),X44)
        | ~ r2_hidden(X46,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49)
        | X48 != X49
        | k1_relat_1(X49) != X43
        | ~ r1_tarski(k2_relat_1(X49),X44)
        | r2_hidden(X48,X45)
        | X45 != k1_funct_2(X43,X44) )
      & ( ~ r2_hidden(esk9_3(X50,X51,X52),X52)
        | ~ v1_relat_1(X54)
        | ~ v1_funct_1(X54)
        | esk9_3(X50,X51,X52) != X54
        | k1_relat_1(X54) != X50
        | ~ r1_tarski(k2_relat_1(X54),X51)
        | X52 = k1_funct_2(X50,X51) )
      & ( v1_relat_1(esk10_3(X50,X51,X52))
        | r2_hidden(esk9_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) )
      & ( v1_funct_1(esk10_3(X50,X51,X52))
        | r2_hidden(esk9_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) )
      & ( esk9_3(X50,X51,X52) = esk10_3(X50,X51,X52)
        | r2_hidden(esk9_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) )
      & ( k1_relat_1(esk10_3(X50,X51,X52)) = X50
        | r2_hidden(esk9_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) )
      & ( r1_tarski(k2_relat_1(esk10_3(X50,X51,X52)),X51)
        | r2_hidden(esk9_3(X50,X51,X52),X52)
        | X52 = k1_funct_2(X50,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_12,plain,
    ( v1_funct_1(esk8_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_13,plain,
    ( X1 = esk8_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_15,plain,
    ( k1_relat_1(esk8_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(esk8_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_funct_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( esk8_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( r2_hidden(esk14_0,k1_funct_2(esk12_0,esk13_0))
    & ( ~ v1_funct_1(esk14_0)
      | ~ v1_funct_2(esk14_0,esk12_0,esk13_0)
      | ~ m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X57,X58,X59] :
      ( ( v1_funct_1(X59)
        | r2_hidden(esk11_3(X57,X58,X59),X57)
        | k1_relat_1(X59) != X57
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( v1_funct_2(X59,X57,X58)
        | r2_hidden(esk11_3(X57,X58,X59),X57)
        | k1_relat_1(X59) != X57
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
        | r2_hidden(esk11_3(X57,X58,X59),X57)
        | k1_relat_1(X59) != X57
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( v1_funct_1(X59)
        | ~ r2_hidden(k1_funct_1(X59,esk11_3(X57,X58,X59)),X58)
        | k1_relat_1(X59) != X57
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( v1_funct_2(X59,X57,X58)
        | ~ r2_hidden(k1_funct_1(X59,esk11_3(X57,X58,X59)),X58)
        | k1_relat_1(X59) != X57
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
        | ~ r2_hidden(k1_funct_1(X59,esk11_3(X57,X58,X59)),X58)
        | k1_relat_1(X59) != X57
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk14_0,k1_funct_2(esk12_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk11_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

fof(c_0_28,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k4_tarski(X19,esk3_3(X17,X18,X19)),X17)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),X17)
        | r2_hidden(X21,X18)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(esk4_2(X23,X24),X24)
        | ~ r2_hidden(k4_tarski(esk4_2(X23,X24),X26),X23)
        | X24 = k1_relat_1(X23) )
      & ( r2_hidden(esk4_2(X23,X24),X24)
        | r2_hidden(k4_tarski(esk4_2(X23,X24),esk5_2(X23,X24)),X23)
        | X24 = k1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_funct_1(esk14_0)
    | ~ v1_funct_2(esk14_0,esk12_0,esk13_0)
    | ~ m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | r2_hidden(esk11_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(esk14_0) = esk12_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_34,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk11_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_35,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_funct_2(esk14_0,esk12_0,esk13_0)
    | ~ m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,X1)))
    | r2_hidden(esk11_3(esk12_0,X1,esk14_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_32]),c_0_32]),c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | r2_hidden(esk11_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ r1_tarski(k1_relat_1(X30),X28)
      | ~ r1_tarski(k2_relat_1(X30),X29)
      | m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_43,plain,(
    ! [X31,X32,X33,X34] :
      ( ( X31 = k4_tarski(esk6_4(X31,X32,X33,X34),esk7_4(X31,X32,X33,X34))
        | ~ r2_hidden(X31,X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( r2_hidden(esk6_4(X31,X32,X33,X34),X32)
        | ~ r2_hidden(X31,X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( r2_hidden(esk7_4(X31,X32,X33,X34),X33)
        | ~ r2_hidden(X31,X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).

fof(c_0_44,plain,(
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

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk11_3(esk12_0,esk13_0,esk14_0),esk12_0)
    | ~ v1_funct_2(esk14_0,esk12_0,esk13_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk14_0,esk12_0,X1)
    | r2_hidden(esk11_3(esk12_0,X1,esk14_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_32]),c_0_32]),c_0_32]),c_0_33])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_50,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_2(esk14_0,esk12_0,esk13_0)
    | ~ v1_xboole_0(esk12_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk14_0,esk12_0,X1)
    | ~ v1_xboole_0(esk12_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(X1,esk12_0)
    | ~ v1_xboole_0(esk14_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_32])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_2(esk14_0,esk12_0,esk13_0)
    | ~ v1_relat_1(esk14_0)
    | ~ r1_tarski(k1_relat_1(esk14_0),esk12_0)
    | ~ r1_tarski(k2_relat_1(esk14_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_48])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X37,X38,X39] :
      ( ( v1_funct_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_partfun1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v1_funct_2(X39,X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_partfun1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_59,plain,(
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

cnf(c_0_60,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_61,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,k2_relat_1(esk14_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_30]),c_0_33])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk12_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(esk12_0)
    | ~ v1_xboole_0(esk14_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_funct_2(esk14_0,esk12_0,esk13_0)
    | ~ r1_tarski(k1_relat_1(esk14_0),esk12_0)
    | ~ r1_tarski(k2_relat_1(esk14_0),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_33])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(esk14_0,esk12_0,k2_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_32]),c_0_30]),c_0_33])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(X1,esk14_0)
    | ~ v1_xboole_0(k2_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(esk14_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_relat_1(esk8_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_funct_2(esk14_0,esk12_0,esk13_0)
    | ~ r1_tarski(k2_relat_1(esk14_0),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_32]),c_0_66])])).

cnf(c_0_74,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_67,c_0_48])).

cnf(c_0_75,negated_conjecture,
    ( v1_partfun1(esk14_0,esk12_0)
    | v1_xboole_0(k2_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_62]),c_0_69]),c_0_30])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk14_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_55]),c_0_71])).

cnf(c_0_77,plain,
    ( r1_tarski(k2_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_partfun1(esk14_0,esk12_0)
    | ~ r1_tarski(k2_relat_1(esk14_0),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_30]),c_0_33]),c_0_32]),c_0_66])])).

cnf(c_0_79,negated_conjecture,
    ( v1_partfun1(esk14_0,esk12_0) ),
    inference(sr,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_18])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk14_0),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_24]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:07:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.029 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.20/0.43  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.43  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 0.20/0.43  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.43  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.20/0.43  fof(t6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 0.20/0.43  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.20/0.43  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.43  fof(c_0_11, plain, ![X43, X44, X45, X46, X48, X49, X50, X51, X52, X54]:(((((((v1_relat_1(esk8_4(X43,X44,X45,X46))|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44))&(v1_funct_1(esk8_4(X43,X44,X45,X46))|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44)))&(X46=esk8_4(X43,X44,X45,X46)|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44)))&(k1_relat_1(esk8_4(X43,X44,X45,X46))=X43|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44)))&(r1_tarski(k2_relat_1(esk8_4(X43,X44,X45,X46)),X44)|~r2_hidden(X46,X45)|X45!=k1_funct_2(X43,X44)))&(~v1_relat_1(X49)|~v1_funct_1(X49)|X48!=X49|k1_relat_1(X49)!=X43|~r1_tarski(k2_relat_1(X49),X44)|r2_hidden(X48,X45)|X45!=k1_funct_2(X43,X44)))&((~r2_hidden(esk9_3(X50,X51,X52),X52)|(~v1_relat_1(X54)|~v1_funct_1(X54)|esk9_3(X50,X51,X52)!=X54|k1_relat_1(X54)!=X50|~r1_tarski(k2_relat_1(X54),X51))|X52=k1_funct_2(X50,X51))&(((((v1_relat_1(esk10_3(X50,X51,X52))|r2_hidden(esk9_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51))&(v1_funct_1(esk10_3(X50,X51,X52))|r2_hidden(esk9_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51)))&(esk9_3(X50,X51,X52)=esk10_3(X50,X51,X52)|r2_hidden(esk9_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51)))&(k1_relat_1(esk10_3(X50,X51,X52))=X50|r2_hidden(esk9_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51)))&(r1_tarski(k2_relat_1(esk10_3(X50,X51,X52)),X51)|r2_hidden(esk9_3(X50,X51,X52),X52)|X52=k1_funct_2(X50,X51))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.20/0.43  cnf(c_0_12, plain, (v1_funct_1(esk8_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_13, plain, (X1=esk8_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.20/0.43  cnf(c_0_15, plain, (k1_relat_1(esk8_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_16, plain, (v1_relat_1(esk8_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_17, plain, (v1_funct_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_18, plain, (esk8_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.43  fof(c_0_19, negated_conjecture, (r2_hidden(esk14_0,k1_funct_2(esk12_0,esk13_0))&(~v1_funct_1(esk14_0)|~v1_funct_2(esk14_0,esk12_0,esk13_0)|~m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.43  fof(c_0_20, plain, ![X57, X58, X59]:((((v1_funct_1(X59)|(r2_hidden(esk11_3(X57,X58,X59),X57)|k1_relat_1(X59)!=X57)|(~v1_relat_1(X59)|~v1_funct_1(X59)))&(v1_funct_2(X59,X57,X58)|(r2_hidden(esk11_3(X57,X58,X59),X57)|k1_relat_1(X59)!=X57)|(~v1_relat_1(X59)|~v1_funct_1(X59))))&(m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|(r2_hidden(esk11_3(X57,X58,X59),X57)|k1_relat_1(X59)!=X57)|(~v1_relat_1(X59)|~v1_funct_1(X59))))&(((v1_funct_1(X59)|(~r2_hidden(k1_funct_1(X59,esk11_3(X57,X58,X59)),X58)|k1_relat_1(X59)!=X57)|(~v1_relat_1(X59)|~v1_funct_1(X59)))&(v1_funct_2(X59,X57,X58)|(~r2_hidden(k1_funct_1(X59,esk11_3(X57,X58,X59)),X58)|k1_relat_1(X59)!=X57)|(~v1_relat_1(X59)|~v1_funct_1(X59))))&(m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|(~r2_hidden(k1_funct_1(X59,esk11_3(X57,X58,X59)),X58)|k1_relat_1(X59)!=X57)|(~v1_relat_1(X59)|~v1_funct_1(X59))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.20/0.43  cnf(c_0_21, plain, (k1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_22, plain, (v1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_23, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.43  cnf(c_0_24, negated_conjecture, (r2_hidden(esk14_0,k1_funct_2(esk12_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk11_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_26, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.20/0.43  cnf(c_0_27, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.20/0.43  fof(c_0_28, plain, ![X17, X18, X19, X21, X22, X23, X24, X26]:(((~r2_hidden(X19,X18)|r2_hidden(k4_tarski(X19,esk3_3(X17,X18,X19)),X17)|X18!=k1_relat_1(X17))&(~r2_hidden(k4_tarski(X21,X22),X17)|r2_hidden(X21,X18)|X18!=k1_relat_1(X17)))&((~r2_hidden(esk4_2(X23,X24),X24)|~r2_hidden(k4_tarski(esk4_2(X23,X24),X26),X23)|X24=k1_relat_1(X23))&(r2_hidden(esk4_2(X23,X24),X24)|r2_hidden(k4_tarski(esk4_2(X23,X24),esk5_2(X23,X24)),X23)|X24=k1_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.43  cnf(c_0_29, negated_conjecture, (~v1_funct_1(esk14_0)|~v1_funct_2(esk14_0,esk12_0,esk13_0)|~m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk14_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.43  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|r2_hidden(esk11_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_32, negated_conjecture, (k1_relat_1(esk14_0)=esk12_0), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.20/0.43  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk14_0)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.20/0.43  cnf(c_0_34, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk11_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  fof(c_0_35, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.43  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (~v1_funct_2(esk14_0,esk12_0,esk13_0)|~m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.20/0.43  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,X1)))|r2_hidden(esk11_3(esk12_0,X1,esk14_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_30]), c_0_32]), c_0_32]), c_0_32]), c_0_33])])).
% 0.20/0.43  cnf(c_0_39, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|r2_hidden(esk11_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.43  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.43  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.43  fof(c_0_42, plain, ![X28, X29, X30]:(~v1_relat_1(X30)|(~r1_tarski(k1_relat_1(X30),X28)|~r1_tarski(k2_relat_1(X30),X29)|m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.20/0.43  fof(c_0_43, plain, ![X31, X32, X33, X34]:(((X31=k4_tarski(esk6_4(X31,X32,X33,X34),esk7_4(X31,X32,X33,X34))|~r2_hidden(X31,X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(r2_hidden(esk6_4(X31,X32,X33,X34),X32)|~r2_hidden(X31,X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(r2_hidden(esk7_4(X31,X32,X33,X34),X33)|~r2_hidden(X31,X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).
% 0.20/0.43  fof(c_0_44, plain, ![X56]:(((v1_funct_1(X56)|(~v1_relat_1(X56)|~v1_funct_1(X56)))&(v1_funct_2(X56,k1_relat_1(X56),k2_relat_1(X56))|(~v1_relat_1(X56)|~v1_funct_1(X56))))&(m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X56),k2_relat_1(X56))))|(~v1_relat_1(X56)|~v1_funct_1(X56)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (r2_hidden(esk11_3(esk12_0,esk13_0,esk14_0),esk12_0)|~v1_funct_2(esk14_0,esk12_0,esk13_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk14_0,esk12_0,X1)|r2_hidden(esk11_3(esk12_0,X1,esk14_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_30]), c_0_32]), c_0_32]), c_0_32]), c_0_33])])).
% 0.20/0.43  cnf(c_0_47, plain, (~r2_hidden(X1,k1_relat_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.43  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.43  fof(c_0_49, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.43  cnf(c_0_50, plain, (r2_hidden(esk7_4(X1,X2,X3,X4),X3)|~r2_hidden(X1,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.43  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, (~v1_funct_2(esk14_0,esk12_0,esk13_0)|~v1_xboole_0(esk12_0)), inference(spm,[status(thm)],[c_0_40, c_0_45])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk14_0,esk12_0,X1)|~v1_xboole_0(esk12_0)), inference(spm,[status(thm)],[c_0_40, c_0_46])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (~r2_hidden(X1,esk12_0)|~v1_xboole_0(esk14_0)), inference(spm,[status(thm)],[c_0_47, c_0_32])).
% 0.20/0.43  cnf(c_0_55, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (~v1_funct_2(esk14_0,esk12_0,esk13_0)|~v1_relat_1(esk14_0)|~r1_tarski(k1_relat_1(esk14_0),esk12_0)|~r1_tarski(k2_relat_1(esk14_0),esk13_0)), inference(spm,[status(thm)],[c_0_37, c_0_48])).
% 0.20/0.43  cnf(c_0_57, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.43  fof(c_0_58, plain, ![X37, X38, X39]:((v1_funct_1(X39)|(~v1_funct_1(X39)|~v1_partfun1(X39,X37))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v1_funct_2(X39,X37,X38)|(~v1_funct_1(X39)|~v1_partfun1(X39,X37))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.20/0.43  fof(c_0_59, plain, ![X40, X41, X42]:((v1_funct_1(X42)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_xboole_0(X41))&(v1_partfun1(X42,X40)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_xboole_0(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.43  cnf(c_0_60, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.43  cnf(c_0_61, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_40, c_0_50])).
% 0.20/0.43  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,k2_relat_1(esk14_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_32]), c_0_30]), c_0_33])])).
% 0.20/0.43  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(esk12_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.43  cnf(c_0_64, negated_conjecture, (v1_xboole_0(esk12_0)|~v1_xboole_0(esk14_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.43  cnf(c_0_65, negated_conjecture, (~v1_funct_2(esk14_0,esk12_0,esk13_0)|~r1_tarski(k1_relat_1(esk14_0),esk12_0)|~r1_tarski(k2_relat_1(esk14_0),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_33])])).
% 0.20/0.43  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_57])).
% 0.20/0.43  cnf(c_0_67, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.43  cnf(c_0_68, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.43  cnf(c_0_69, negated_conjecture, (v1_funct_2(esk14_0,esk12_0,k2_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_32]), c_0_30]), c_0_33])])).
% 0.20/0.43  cnf(c_0_70, negated_conjecture, (~r2_hidden(X1,esk14_0)|~v1_xboole_0(k2_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.43  cnf(c_0_71, negated_conjecture, (~v1_xboole_0(esk14_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.43  cnf(c_0_72, plain, (r1_tarski(k2_relat_1(esk8_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_73, negated_conjecture, (~v1_funct_2(esk14_0,esk12_0,esk13_0)|~r1_tarski(k2_relat_1(esk14_0),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_32]), c_0_66])])).
% 0.20/0.43  cnf(c_0_74, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_67, c_0_48])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, (v1_partfun1(esk14_0,esk12_0)|v1_xboole_0(k2_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_62]), c_0_69]), c_0_30])])).
% 0.20/0.43  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk14_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_55]), c_0_71])).
% 0.20/0.43  cnf(c_0_77, plain, (r1_tarski(k2_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_72])).
% 0.20/0.43  cnf(c_0_78, negated_conjecture, (~v1_partfun1(esk14_0,esk12_0)|~r1_tarski(k2_relat_1(esk14_0),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_30]), c_0_33]), c_0_32]), c_0_66])])).
% 0.20/0.43  cnf(c_0_79, negated_conjecture, (v1_partfun1(esk14_0,esk12_0)), inference(sr,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.43  cnf(c_0_80, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_77, c_0_18])).
% 0.20/0.43  cnf(c_0_81, negated_conjecture, (~r1_tarski(k2_relat_1(esk14_0),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 0.20/0.43  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_24]), c_0_81]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 83
% 0.20/0.43  # Proof object clause steps            : 60
% 0.20/0.43  # Proof object formula steps           : 23
% 0.20/0.43  # Proof object conjectures             : 30
% 0.20/0.43  # Proof object clause conjectures      : 27
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 19
% 0.20/0.43  # Proof object initial formulas used   : 11
% 0.20/0.43  # Proof object generating inferences   : 27
% 0.20/0.43  # Proof object simplifying inferences  : 45
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 14
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 44
% 0.20/0.43  # Removed in clause preprocessing      : 5
% 0.20/0.43  # Initial clauses in saturation        : 39
% 0.20/0.43  # Processed clauses                    : 876
% 0.20/0.43  # ...of these trivial                  : 1
% 0.20/0.43  # ...subsumed                          : 540
% 0.20/0.43  # ...remaining for further processing  : 335
% 0.20/0.43  # Other redundant clauses eliminated   : 17
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 23
% 0.20/0.43  # Backward-rewritten                   : 13
% 0.20/0.43  # Generated clauses                    : 2069
% 0.20/0.43  # ...of the previous two non-trivial   : 1778
% 0.20/0.43  # Contextual simplify-reflections      : 15
% 0.20/0.43  # Paramodulations                      : 2053
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 17
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 245
% 0.20/0.43  #    Positive orientable unit clauses  : 13
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 10
% 0.20/0.44  #    Non-unit-clauses                  : 222
% 0.20/0.44  # Current number of unprocessed clauses: 935
% 0.20/0.44  # ...number of literals in the above   : 3740
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 75
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 8246
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 4619
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 209
% 0.20/0.44  # Unit Clause-clause subsumption calls : 411
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 11
% 0.20/0.44  # BW rewrite match successes           : 8
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 29868
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.079 s
% 0.20/0.44  # System time              : 0.005 s
% 0.20/0.44  # Total time               : 0.084 s
% 0.20/0.44  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
