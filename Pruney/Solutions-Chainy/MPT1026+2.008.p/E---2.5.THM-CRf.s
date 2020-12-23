%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 444 expanded)
%              Number of clauses        :   51 ( 225 expanded)
%              Number of leaves         :   11 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (3551 expanded)
%              Number of equality atoms :   51 (1314 expanded)
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

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

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

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_11,plain,(
    ! [X46,X47,X48,X49,X51,X52,X53,X54,X55,X57] :
      ( ( v1_relat_1(esk8_4(X46,X47,X48,X49))
        | ~ r2_hidden(X49,X48)
        | X48 != k1_funct_2(X46,X47) )
      & ( v1_funct_1(esk8_4(X46,X47,X48,X49))
        | ~ r2_hidden(X49,X48)
        | X48 != k1_funct_2(X46,X47) )
      & ( X49 = esk8_4(X46,X47,X48,X49)
        | ~ r2_hidden(X49,X48)
        | X48 != k1_funct_2(X46,X47) )
      & ( k1_relat_1(esk8_4(X46,X47,X48,X49)) = X46
        | ~ r2_hidden(X49,X48)
        | X48 != k1_funct_2(X46,X47) )
      & ( r1_tarski(k2_relat_1(esk8_4(X46,X47,X48,X49)),X47)
        | ~ r2_hidden(X49,X48)
        | X48 != k1_funct_2(X46,X47) )
      & ( ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52)
        | X51 != X52
        | k1_relat_1(X52) != X46
        | ~ r1_tarski(k2_relat_1(X52),X47)
        | r2_hidden(X51,X48)
        | X48 != k1_funct_2(X46,X47) )
      & ( ~ r2_hidden(esk9_3(X53,X54,X55),X55)
        | ~ v1_relat_1(X57)
        | ~ v1_funct_1(X57)
        | esk9_3(X53,X54,X55) != X57
        | k1_relat_1(X57) != X53
        | ~ r1_tarski(k2_relat_1(X57),X54)
        | X55 = k1_funct_2(X53,X54) )
      & ( v1_relat_1(esk10_3(X53,X54,X55))
        | r2_hidden(esk9_3(X53,X54,X55),X55)
        | X55 = k1_funct_2(X53,X54) )
      & ( v1_funct_1(esk10_3(X53,X54,X55))
        | r2_hidden(esk9_3(X53,X54,X55),X55)
        | X55 = k1_funct_2(X53,X54) )
      & ( esk9_3(X53,X54,X55) = esk10_3(X53,X54,X55)
        | r2_hidden(esk9_3(X53,X54,X55),X55)
        | X55 = k1_funct_2(X53,X54) )
      & ( k1_relat_1(esk10_3(X53,X54,X55)) = X53
        | r2_hidden(esk9_3(X53,X54,X55),X55)
        | X55 = k1_funct_2(X53,X54) )
      & ( r1_tarski(k2_relat_1(esk10_3(X53,X54,X55)),X54)
        | r2_hidden(esk9_3(X53,X54,X55),X55)
        | X55 = k1_funct_2(X53,X54) ) ) ),
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
    ( v1_funct_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( esk8_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,
    ( r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0))
    & ( ~ v1_funct_1(esk13_0)
      | ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
      | ~ m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_18,plain,
    ( v1_relat_1(esk8_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_relat_1(esk8_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_funct_1(esk13_0)
    | ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
    | ~ m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk13_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ r1_tarski(k1_relat_1(X36),X34)
      | ~ r1_tarski(k2_relat_1(X36),X35)
      | m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_27,plain,
    ( k1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
    | ~ m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_32,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
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

cnf(c_0_35,plain,
    ( r1_tarski(k2_relat_1(esk8_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_36,plain,(
    ! [X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(k4_tarski(X14,esk2_3(X12,X13,X14)),X12)
        | X13 != k1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X16,X17),X12)
        | r2_hidden(X16,X13)
        | X13 != k1_relat_1(X12) )
      & ( ~ r2_hidden(esk3_2(X18,X19),X19)
        | ~ r2_hidden(k4_tarski(esk3_2(X18,X19),X21),X18)
        | X19 = k1_relat_1(X18) )
      & ( r2_hidden(esk3_2(X18,X19),X19)
        | r2_hidden(k4_tarski(esk3_2(X18,X19),esk4_2(X18,X19)),X18)
        | X19 = k1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_37,plain,(
    ! [X59] :
      ( ( v1_funct_1(X59)
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( v1_funct_2(X59,k1_relat_1(X59),k2_relat_1(X59))
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X59),k2_relat_1(X59))))
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
    | ~ r1_tarski(k1_relat_1(esk13_0),esk11_0)
    | ~ r1_tarski(k2_relat_1(esk13_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk13_0) = esk11_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_20])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( ~ r2_hidden(X25,X24)
        | r2_hidden(k4_tarski(esk5_3(X23,X24,X25),X25),X23)
        | X24 != k2_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X28,X27),X23)
        | r2_hidden(X27,X24)
        | X24 != k2_relat_1(X23) )
      & ( ~ r2_hidden(esk6_2(X29,X30),X30)
        | ~ r2_hidden(k4_tarski(X32,esk6_2(X29,X30)),X29)
        | X30 = k2_relat_1(X29) )
      & ( r2_hidden(esk6_2(X29,X30),X30)
        | r2_hidden(k4_tarski(esk7_2(X29,X30),esk6_2(X29,X30)),X29)
        | X30 = k2_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X43,X44,X45] :
      ( ( v1_funct_1(X45)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | v1_xboole_0(X44) )
      & ( v1_partfun1(X45,X43)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | v1_xboole_0(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
    | ~ r1_tarski(k2_relat_1(esk13_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_49,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_16])).

fof(c_0_51,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_xboole_0(X40)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | v1_partfun1(X42,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_52,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,k2_relat_1(esk13_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_39]),c_0_24]),c_0_31])])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk13_0,esk11_0,k2_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_39]),c_0_24]),c_0_31])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_partfun1(esk13_0,esk11_0)
    | ~ r1_tarski(k2_relat_1(esk13_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_24]),c_0_31]),c_0_39]),c_0_40])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk13_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_20])).

cnf(c_0_59,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_60,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_3(esk13_0,esk11_0,X1)),esk13_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_39])).

cnf(c_0_63,negated_conjecture,
    ( v1_partfun1(esk13_0,esk11_0)
    | v1_xboole_0(k2_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_24])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_partfun1(esk13_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_65,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_66,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_3(esk13_0,esk11_0,X1),k2_relat_1(esk13_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk13_0)) ),
    inference(sr,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( v1_partfun1(esk13_0,esk11_0)
    | ~ v1_xboole_0(esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_39]),c_0_24]),c_0_31])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(X1,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_71,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk11_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:27:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.19/0.40  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.19/0.40  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.19/0.40  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.40  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.40  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.40  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.19/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.40  fof(c_0_11, plain, ![X46, X47, X48, X49, X51, X52, X53, X54, X55, X57]:(((((((v1_relat_1(esk8_4(X46,X47,X48,X49))|~r2_hidden(X49,X48)|X48!=k1_funct_2(X46,X47))&(v1_funct_1(esk8_4(X46,X47,X48,X49))|~r2_hidden(X49,X48)|X48!=k1_funct_2(X46,X47)))&(X49=esk8_4(X46,X47,X48,X49)|~r2_hidden(X49,X48)|X48!=k1_funct_2(X46,X47)))&(k1_relat_1(esk8_4(X46,X47,X48,X49))=X46|~r2_hidden(X49,X48)|X48!=k1_funct_2(X46,X47)))&(r1_tarski(k2_relat_1(esk8_4(X46,X47,X48,X49)),X47)|~r2_hidden(X49,X48)|X48!=k1_funct_2(X46,X47)))&(~v1_relat_1(X52)|~v1_funct_1(X52)|X51!=X52|k1_relat_1(X52)!=X46|~r1_tarski(k2_relat_1(X52),X47)|r2_hidden(X51,X48)|X48!=k1_funct_2(X46,X47)))&((~r2_hidden(esk9_3(X53,X54,X55),X55)|(~v1_relat_1(X57)|~v1_funct_1(X57)|esk9_3(X53,X54,X55)!=X57|k1_relat_1(X57)!=X53|~r1_tarski(k2_relat_1(X57),X54))|X55=k1_funct_2(X53,X54))&(((((v1_relat_1(esk10_3(X53,X54,X55))|r2_hidden(esk9_3(X53,X54,X55),X55)|X55=k1_funct_2(X53,X54))&(v1_funct_1(esk10_3(X53,X54,X55))|r2_hidden(esk9_3(X53,X54,X55),X55)|X55=k1_funct_2(X53,X54)))&(esk9_3(X53,X54,X55)=esk10_3(X53,X54,X55)|r2_hidden(esk9_3(X53,X54,X55),X55)|X55=k1_funct_2(X53,X54)))&(k1_relat_1(esk10_3(X53,X54,X55))=X53|r2_hidden(esk9_3(X53,X54,X55),X55)|X55=k1_funct_2(X53,X54)))&(r1_tarski(k2_relat_1(esk10_3(X53,X54,X55)),X54)|r2_hidden(esk9_3(X53,X54,X55),X55)|X55=k1_funct_2(X53,X54))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.19/0.40  cnf(c_0_12, plain, (v1_funct_1(esk8_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_13, plain, (X1=esk8_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.19/0.40  cnf(c_0_15, plain, (v1_funct_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_16, plain, (esk8_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.19/0.40  fof(c_0_17, negated_conjecture, (r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0))&(~v1_funct_1(esk13_0)|~v1_funct_2(esk13_0,esk11_0,esk12_0)|~m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.40  cnf(c_0_18, plain, (v1_relat_1(esk8_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_19, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_21, plain, (v1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_22, plain, (k1_relat_1(esk8_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (~v1_funct_1(esk13_0)|~v1_funct_2(esk13_0,esk11_0,esk12_0)|~m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk13_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.40  fof(c_0_25, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|(~r1_tarski(k1_relat_1(X36),X34)|~r1_tarski(k2_relat_1(X36),X35)|m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.40  cnf(c_0_26, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_16])).
% 0.19/0.40  cnf(c_0_27, plain, (k1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.40  fof(c_0_28, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (~v1_funct_2(esk13_0,esk11_0,esk12_0)|~m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])])).
% 0.19/0.40  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk13_0)), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.19/0.40  cnf(c_0_32, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_16])).
% 0.19/0.40  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  fof(c_0_34, plain, ![X37, X38, X39]:((v1_funct_1(X39)|(~v1_funct_1(X39)|~v1_partfun1(X39,X37))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v1_funct_2(X39,X37,X38)|(~v1_funct_1(X39)|~v1_partfun1(X39,X37))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.19/0.40  cnf(c_0_35, plain, (r1_tarski(k2_relat_1(esk8_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  fof(c_0_36, plain, ![X12, X13, X14, X16, X17, X18, X19, X21]:(((~r2_hidden(X14,X13)|r2_hidden(k4_tarski(X14,esk2_3(X12,X13,X14)),X12)|X13!=k1_relat_1(X12))&(~r2_hidden(k4_tarski(X16,X17),X12)|r2_hidden(X16,X13)|X13!=k1_relat_1(X12)))&((~r2_hidden(esk3_2(X18,X19),X19)|~r2_hidden(k4_tarski(esk3_2(X18,X19),X21),X18)|X19=k1_relat_1(X18))&(r2_hidden(esk3_2(X18,X19),X19)|r2_hidden(k4_tarski(esk3_2(X18,X19),esk4_2(X18,X19)),X18)|X19=k1_relat_1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.40  fof(c_0_37, plain, ![X59]:(((v1_funct_1(X59)|(~v1_relat_1(X59)|~v1_funct_1(X59)))&(v1_funct_2(X59,k1_relat_1(X59),k2_relat_1(X59))|(~v1_relat_1(X59)|~v1_funct_1(X59))))&(m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X59),k2_relat_1(X59))))|(~v1_relat_1(X59)|~v1_funct_1(X59)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (~v1_funct_2(esk13_0,esk11_0,esk12_0)|~r1_tarski(k1_relat_1(esk13_0),esk11_0)|~r1_tarski(k2_relat_1(esk13_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk13_0)=esk11_0), inference(spm,[status(thm)],[c_0_32, c_0_20])).
% 0.19/0.40  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_41, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_42, plain, (r1_tarski(k2_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_35])).
% 0.19/0.40  fof(c_0_43, plain, ![X23, X24, X25, X27, X28, X29, X30, X32]:(((~r2_hidden(X25,X24)|r2_hidden(k4_tarski(esk5_3(X23,X24,X25),X25),X23)|X24!=k2_relat_1(X23))&(~r2_hidden(k4_tarski(X28,X27),X23)|r2_hidden(X27,X24)|X24!=k2_relat_1(X23)))&((~r2_hidden(esk6_2(X29,X30),X30)|~r2_hidden(k4_tarski(X32,esk6_2(X29,X30)),X29)|X30=k2_relat_1(X29))&(r2_hidden(esk6_2(X29,X30),X30)|r2_hidden(k4_tarski(esk7_2(X29,X30),esk6_2(X29,X30)),X29)|X30=k2_relat_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.40  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.40  fof(c_0_45, plain, ![X43, X44, X45]:((v1_funct_1(X45)|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_xboole_0(X44))&(v1_partfun1(X45,X43)|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_xboole_0(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.40  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_47, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (~v1_funct_2(esk13_0,esk11_0,esk12_0)|~r1_tarski(k2_relat_1(esk13_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.19/0.40  cnf(c_0_49, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_41, c_0_30])).
% 0.19/0.40  cnf(c_0_50, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_42, c_0_16])).
% 0.19/0.40  fof(c_0_51, plain, ![X40, X41, X42]:(~v1_xboole_0(X40)|(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_partfun1(X42,X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.19/0.40  cnf(c_0_52, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.40  cnf(c_0_53, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_44])).
% 0.19/0.40  cnf(c_0_54, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,k2_relat_1(esk13_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_39]), c_0_24]), c_0_31])])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk13_0,esk11_0,k2_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_39]), c_0_24]), c_0_31])])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (~v1_partfun1(esk13_0,esk11_0)|~r1_tarski(k2_relat_1(esk13_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_24]), c_0_31]), c_0_39]), c_0_40])])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_relat_1(esk13_0),esk12_0)), inference(spm,[status(thm)],[c_0_50, c_0_20])).
% 0.19/0.40  cnf(c_0_59, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.40  fof(c_0_60, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.40  cnf(c_0_61, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_52])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_3(esk13_0,esk11_0,X1)),esk13_0)|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_53, c_0_39])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (v1_partfun1(esk13_0,esk11_0)|v1_xboole_0(k2_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_24])])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (~v1_partfun1(esk13_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.19/0.40  cnf(c_0_65, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 0.19/0.40  cnf(c_0_66, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_3(esk13_0,esk11_0,X1),k2_relat_1(esk13_0))|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (v1_xboole_0(k2_relat_1(esk13_0))), inference(sr,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (v1_partfun1(esk13_0,esk11_0)|~v1_xboole_0(esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_39]), c_0_24]), c_0_31])])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (~r2_hidden(X1,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 0.19/0.40  cnf(c_0_71, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (~v1_xboole_0(esk11_0)), inference(spm,[status(thm)],[c_0_64, c_0_69])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 74
% 0.19/0.40  # Proof object clause steps            : 51
% 0.19/0.40  # Proof object formula steps           : 23
% 0.19/0.40  # Proof object conjectures             : 24
% 0.19/0.40  # Proof object clause conjectures      : 21
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 18
% 0.19/0.40  # Proof object initial formulas used   : 11
% 0.19/0.40  # Proof object generating inferences   : 21
% 0.19/0.40  # Proof object simplifying inferences  : 38
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 11
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 36
% 0.19/0.40  # Removed in clause preprocessing      : 3
% 0.19/0.40  # Initial clauses in saturation        : 33
% 0.19/0.40  # Processed clauses                    : 327
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 46
% 0.19/0.40  # ...remaining for further processing  : 281
% 0.19/0.40  # Other redundant clauses eliminated   : 15
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 4
% 0.19/0.40  # Generated clauses                    : 1442
% 0.19/0.40  # ...of the previous two non-trivial   : 1426
% 0.19/0.40  # Contextual simplify-reflections      : 1
% 0.19/0.40  # Paramodulations                      : 1428
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 15
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 231
% 0.19/0.40  #    Positive orientable unit clauses  : 9
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 6
% 0.19/0.40  #    Non-unit-clauses                  : 216
% 0.19/0.40  # Current number of unprocessed clauses: 1160
% 0.19/0.40  # ...number of literals in the above   : 3299
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 37
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 11691
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 8930
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 45
% 0.19/0.40  # Unit Clause-clause subsumption calls : 308
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 5
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 20772
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.059 s
% 0.19/0.40  # System time              : 0.009 s
% 0.19/0.40  # Total time               : 0.068 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
