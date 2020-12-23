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
% DateTime   : Thu Dec  3 11:06:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 (3285 expanded)
%              Number of clauses        :   81 (1516 expanded)
%              Number of leaves         :   13 ( 734 expanded)
%              Depth                    :   18
%              Number of atoms          :  366 (22832 expanded)
%              Number of equality atoms :   70 (7798 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

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

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

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

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X49,X50,X51,X52,X54,X55,X56,X57,X58,X60] :
      ( ( v1_relat_1(esk5_4(X49,X50,X51,X52))
        | ~ r2_hidden(X52,X51)
        | X51 != k1_funct_2(X49,X50) )
      & ( v1_funct_1(esk5_4(X49,X50,X51,X52))
        | ~ r2_hidden(X52,X51)
        | X51 != k1_funct_2(X49,X50) )
      & ( X52 = esk5_4(X49,X50,X51,X52)
        | ~ r2_hidden(X52,X51)
        | X51 != k1_funct_2(X49,X50) )
      & ( k1_relat_1(esk5_4(X49,X50,X51,X52)) = X49
        | ~ r2_hidden(X52,X51)
        | X51 != k1_funct_2(X49,X50) )
      & ( r1_tarski(k2_relat_1(esk5_4(X49,X50,X51,X52)),X50)
        | ~ r2_hidden(X52,X51)
        | X51 != k1_funct_2(X49,X50) )
      & ( ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55)
        | X54 != X55
        | k1_relat_1(X55) != X49
        | ~ r1_tarski(k2_relat_1(X55),X50)
        | r2_hidden(X54,X51)
        | X51 != k1_funct_2(X49,X50) )
      & ( ~ r2_hidden(esk6_3(X56,X57,X58),X58)
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60)
        | esk6_3(X56,X57,X58) != X60
        | k1_relat_1(X60) != X56
        | ~ r1_tarski(k2_relat_1(X60),X57)
        | X58 = k1_funct_2(X56,X57) )
      & ( v1_relat_1(esk7_3(X56,X57,X58))
        | r2_hidden(esk6_3(X56,X57,X58),X58)
        | X58 = k1_funct_2(X56,X57) )
      & ( v1_funct_1(esk7_3(X56,X57,X58))
        | r2_hidden(esk6_3(X56,X57,X58),X58)
        | X58 = k1_funct_2(X56,X57) )
      & ( esk6_3(X56,X57,X58) = esk7_3(X56,X57,X58)
        | r2_hidden(esk6_3(X56,X57,X58),X58)
        | X58 = k1_funct_2(X56,X57) )
      & ( k1_relat_1(esk7_3(X56,X57,X58)) = X56
        | r2_hidden(esk6_3(X56,X57,X58),X58)
        | X58 = k1_funct_2(X56,X57) )
      & ( r1_tarski(k2_relat_1(esk7_3(X56,X57,X58)),X57)
        | r2_hidden(esk6_3(X56,X57,X58),X58)
        | X58 = k1_funct_2(X56,X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

fof(c_0_16,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X1 = esk5_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,negated_conjecture,
    ( r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0))
    & ( ~ v1_funct_1(esk10_0)
      | ~ v1_funct_2(esk10_0,esk8_0,esk9_0)
      | ~ m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | ~ v1_xboole_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_relat_1(esk5_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( esk5_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_funct_1(esk5_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( v1_relat_1(esk5_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_30,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_31,plain,(
    ! [X63] :
      ( ( v1_funct_1(X63)
        | ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63) )
      & ( v1_funct_2(X63,k1_relat_1(X63),k2_relat_1(X63))
        | ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63) )
      & ( m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X63),k2_relat_1(X63))))
        | ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_32,plain,
    ( k1_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( esk5_4(esk8_0,esk9_0,k1_funct_2(esk8_0,esk9_0),esk10_0) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( v1_funct_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( v1_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_relat_1(esk5_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_xboole_0(X37)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))
      | v1_xboole_0(X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_42,plain,(
    ! [X46,X47,X48] :
      ( ( v1_funct_1(X48)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | v1_xboole_0(X47) )
      & ( v1_partfun1(X48,X46)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | v1_xboole_0(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk10_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25])])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_25])])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_25])])).

cnf(c_0_47,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_48,plain,(
    ! [X62] :
      ( v1_partfun1(k6_partfun1(X62),X62)
      & m1_subset_1(k6_partfun1(X62),k1_zfmisc_1(k2_zfmisc_1(X62,X62))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_49,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ r1_tarski(k1_relat_1(X42),X40)
      | ~ r1_tarski(k2_relat_1(X42),X41)
      | m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_57,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk10_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_33]),c_0_25])])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_38])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_52])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_29])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_52])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_43])).

cnf(c_0_65,negated_conjecture,
    ( v1_partfun1(esk10_0,esk8_0)
    | v1_xboole_0(k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_45])])).

cnf(c_0_66,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X1))
    | ~ r2_hidden(X2,k6_partfun1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_funct_1(esk10_0)
    | ~ v1_funct_2(esk10_0,esk8_0,esk9_0)
    | ~ m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk9_0)))
    | ~ r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_46]),c_0_44])])).

cnf(c_0_69,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0)) = esk10_0
    | ~ m1_subset_1(k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0)),k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_55])).

cnf(c_0_70,plain,
    ( m1_subset_1(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_52])).

cnf(c_0_72,negated_conjecture,
    ( v1_partfun1(esk10_0,esk8_0)
    | v1_xboole_0(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_45]),c_0_46])])).

cnf(c_0_73,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k6_partfun1(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_62])).

fof(c_0_74,plain,(
    ! [X43,X44,X45] :
      ( ( v1_funct_1(X45)
        | ~ v1_funct_1(X45)
        | ~ v1_partfun1(X45,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( v1_funct_2(X45,X43,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_partfun1(X45,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_funct_2(esk10_0,esk8_0,esk9_0)
    | ~ m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_45])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_22])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0)) = esk10_0
    | ~ v1_xboole_0(k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( X1 = esk10_0
    | v1_partfun1(esk10_0,esk8_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,plain,
    ( r1_tarski(k6_partfun1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_40])).

cnf(c_0_80,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_funct_2(esk10_0,esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_82,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0)) = esk10_0
    | v1_partfun1(esk10_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_65])).

cnf(c_0_83,negated_conjecture,
    ( k2_relat_1(esk10_0) = esk10_0
    | v1_partfun1(esk10_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_65])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_85,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_partfun1(esk10_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_76]),c_0_45])]),c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk10_0) = esk10_0
    | v1_partfun1(esk10_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( X1 = k6_partfun1(X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(esk10_0) ),
    inference(sr,[status(thm)],[c_0_72,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk10_0) = esk10_0 ),
    inference(sr,[status(thm)],[c_0_87,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( k6_partfun1(X1) = esk10_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_90]),c_0_89])])).

cnf(c_0_93,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_94,negated_conjecture,
    ( k6_partfun1(X1) = esk10_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

fof(c_0_95,plain,(
    ! [X21,X22,X23,X25,X26,X27,X29] :
      ( ( r2_hidden(esk2_3(X21,X22,X23),k1_relat_1(X21))
        | ~ r2_hidden(X23,X22)
        | X22 != k2_relat_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( X23 = k1_funct_1(X21,esk2_3(X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | X22 != k2_relat_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(X26,k1_relat_1(X21))
        | X25 != k1_funct_1(X21,X26)
        | r2_hidden(X25,X22)
        | X22 != k2_relat_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(esk3_2(X21,X27),X27)
        | ~ r2_hidden(X29,k1_relat_1(X21))
        | esk3_2(X21,X27) != k1_funct_1(X21,X29)
        | X27 = k2_relat_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk4_2(X21,X27),k1_relat_1(X21))
        | r2_hidden(esk3_2(X21,X27),X27)
        | X27 = k2_relat_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( esk3_2(X21,X27) = k1_funct_1(X21,esk4_2(X21,X27))
        | r2_hidden(esk3_2(X21,X27),X27)
        | X27 = k2_relat_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0)))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_55])).

cnf(c_0_97,negated_conjecture,
    ( v1_partfun1(esk10_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_62])).

cnf(c_0_100,negated_conjecture,
    ( k2_relat_1(esk10_0) = esk10_0 ),
    inference(sr,[status(thm)],[c_0_83,c_0_86])).

cnf(c_0_101,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_97])).

cnf(c_0_102,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_40])).

cnf(c_0_103,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_98])])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_hidden(X1,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100]),c_0_89])])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_100]),c_0_45]),c_0_46]),c_0_44])]),c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_105,c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic U_____100_C09_12_F1_SE_CS_SP_PS_S5PRR_RG_ND_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.029 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.20/0.41  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.41  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.41  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.20/0.41  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.41  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.41  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.20/0.41  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.20/0.41  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.41  fof(c_0_13, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  fof(c_0_14, plain, ![X49, X50, X51, X52, X54, X55, X56, X57, X58, X60]:(((((((v1_relat_1(esk5_4(X49,X50,X51,X52))|~r2_hidden(X52,X51)|X51!=k1_funct_2(X49,X50))&(v1_funct_1(esk5_4(X49,X50,X51,X52))|~r2_hidden(X52,X51)|X51!=k1_funct_2(X49,X50)))&(X52=esk5_4(X49,X50,X51,X52)|~r2_hidden(X52,X51)|X51!=k1_funct_2(X49,X50)))&(k1_relat_1(esk5_4(X49,X50,X51,X52))=X49|~r2_hidden(X52,X51)|X51!=k1_funct_2(X49,X50)))&(r1_tarski(k2_relat_1(esk5_4(X49,X50,X51,X52)),X50)|~r2_hidden(X52,X51)|X51!=k1_funct_2(X49,X50)))&(~v1_relat_1(X55)|~v1_funct_1(X55)|X54!=X55|k1_relat_1(X55)!=X49|~r1_tarski(k2_relat_1(X55),X50)|r2_hidden(X54,X51)|X51!=k1_funct_2(X49,X50)))&((~r2_hidden(esk6_3(X56,X57,X58),X58)|(~v1_relat_1(X60)|~v1_funct_1(X60)|esk6_3(X56,X57,X58)!=X60|k1_relat_1(X60)!=X56|~r1_tarski(k2_relat_1(X60),X57))|X58=k1_funct_2(X56,X57))&(((((v1_relat_1(esk7_3(X56,X57,X58))|r2_hidden(esk6_3(X56,X57,X58),X58)|X58=k1_funct_2(X56,X57))&(v1_funct_1(esk7_3(X56,X57,X58))|r2_hidden(esk6_3(X56,X57,X58),X58)|X58=k1_funct_2(X56,X57)))&(esk6_3(X56,X57,X58)=esk7_3(X56,X57,X58)|r2_hidden(esk6_3(X56,X57,X58),X58)|X58=k1_funct_2(X56,X57)))&(k1_relat_1(esk7_3(X56,X57,X58))=X56|r2_hidden(esk6_3(X56,X57,X58),X58)|X58=k1_funct_2(X56,X57)))&(r1_tarski(k2_relat_1(esk7_3(X56,X57,X58)),X57)|r2_hidden(esk6_3(X56,X57,X58),X58)|X58=k1_funct_2(X56,X57))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.20/0.41  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.20/0.41  fof(c_0_16, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_18, plain, (X1=esk5_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_19, negated_conjecture, (r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0))&(~v1_funct_1(esk10_0)|~v1_funct_2(esk10_0,esk8_0,esk9_0)|~m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.41  fof(c_0_20, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|~v1_xboole_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.41  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_22, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_23, plain, (k1_relat_1(esk5_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_24, plain, (esk5_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_26, plain, (v1_funct_1(esk5_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_27, plain, (v1_relat_1(esk5_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  fof(c_0_30, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.41  fof(c_0_31, plain, ![X63]:(((v1_funct_1(X63)|(~v1_relat_1(X63)|~v1_funct_1(X63)))&(v1_funct_2(X63,k1_relat_1(X63),k2_relat_1(X63))|(~v1_relat_1(X63)|~v1_funct_1(X63))))&(m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X63),k2_relat_1(X63))))|(~v1_relat_1(X63)|~v1_funct_1(X63)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.41  cnf(c_0_32, plain, (k1_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (esk5_4(esk8_0,esk9_0,k1_funct_2(esk8_0,esk9_0),esk10_0)=esk10_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.41  cnf(c_0_34, plain, (v1_funct_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_35, plain, (v1_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_36, plain, (r1_tarski(k2_relat_1(esk5_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_39, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  fof(c_0_41, plain, ![X37, X38, X39]:(~v1_xboole_0(X37)|(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))|v1_xboole_0(X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.20/0.41  fof(c_0_42, plain, ![X46, X47, X48]:((v1_funct_1(X48)|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|v1_xboole_0(X47))&(v1_partfun1(X48,X46)|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|v1_xboole_0(X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.41  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk10_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25])])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_25])])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_33]), c_0_25])])).
% 0.20/0.41  cnf(c_0_47, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  fof(c_0_48, plain, ![X62]:(v1_partfun1(k6_partfun1(X62),X62)&m1_subset_1(k6_partfun1(X62),k1_zfmisc_1(k2_zfmisc_1(X62,X62)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.41  fof(c_0_49, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|(~r1_tarski(k1_relat_1(X42),X40)|~r1_tarski(k2_relat_1(X42),X41)|m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.20/0.41  cnf(c_0_50, plain, (r1_tarski(k2_relat_1(esk5_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_51, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.41  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.41  cnf(c_0_53, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.41  cnf(c_0_54, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_44]), c_0_45]), c_0_46])])).
% 0.20/0.41  cnf(c_0_57, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.41  cnf(c_0_58, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (r1_tarski(k2_relat_1(esk10_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_33]), c_0_25])])).
% 0.20/0.41  cnf(c_0_60, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_51, c_0_38])).
% 0.20/0.41  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_52])).
% 0.20/0.41  cnf(c_0_62, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_53, c_0_29])).
% 0.20/0.41  cnf(c_0_63, plain, (X1=X2|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_52])).
% 0.20/0.41  cnf(c_0_64, plain, (v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_43])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (v1_partfun1(esk10_0,esk8_0)|v1_xboole_0(k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_45])])).
% 0.20/0.41  cnf(c_0_66, plain, (~v1_xboole_0(k2_zfmisc_1(X1,X1))|~r2_hidden(X2,k6_partfun1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_57])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (~v1_funct_1(esk10_0)|~v1_funct_2(esk10_0,esk8_0,esk9_0)|~m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk9_0)))|~r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_46]), c_0_44])])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0))=esk10_0|~m1_subset_1(k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0)),k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_60, c_0_55])).
% 0.20/0.41  cnf(c_0_70, plain, (m1_subset_1(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.41  cnf(c_0_71, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_63, c_0_52])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (v1_partfun1(esk10_0,esk8_0)|v1_xboole_0(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_45]), c_0_46])])).
% 0.20/0.41  cnf(c_0_73, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k6_partfun1(X1))), inference(spm,[status(thm)],[c_0_66, c_0_62])).
% 0.20/0.41  fof(c_0_74, plain, ![X43, X44, X45]:((v1_funct_1(X45)|(~v1_funct_1(X45)|~v1_partfun1(X45,X43))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))&(v1_funct_2(X45,X43,X44)|(~v1_funct_1(X45)|~v1_partfun1(X45,X43))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (~v1_funct_2(esk10_0,esk8_0,esk9_0)|~m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_45])])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_68, c_0_22])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0))=esk10_0|~v1_xboole_0(k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (X1=esk10_0|v1_partfun1(esk10_0,esk8_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.41  cnf(c_0_79, plain, (r1_tarski(k6_partfun1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_73, c_0_40])).
% 0.20/0.41  cnf(c_0_80, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, (~v1_funct_2(esk10_0,esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0))=esk10_0|v1_partfun1(esk10_0,esk8_0)), inference(spm,[status(thm)],[c_0_77, c_0_65])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (k2_relat_1(esk10_0)=esk10_0|v1_partfun1(esk10_0,esk8_0)), inference(spm,[status(thm)],[c_0_78, c_0_65])).
% 0.20/0.41  cnf(c_0_84, plain, (X1=X2|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.41  cnf(c_0_85, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_79])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (~v1_partfun1(esk10_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_76]), c_0_45])]), c_0_81])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (k2_zfmisc_1(esk8_0,esk10_0)=esk10_0|v1_partfun1(esk10_0,esk8_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.41  cnf(c_0_88, plain, (X1=k6_partfun1(X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (v1_xboole_0(esk10_0)), inference(sr,[status(thm)],[c_0_72, c_0_86])).
% 0.20/0.41  cnf(c_0_90, negated_conjecture, (k2_zfmisc_1(esk8_0,esk10_0)=esk10_0), inference(sr,[status(thm)],[c_0_87, c_0_86])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (k6_partfun1(X1)=esk10_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_90]), c_0_89])])).
% 0.20/0.41  cnf(c_0_93, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.41  cnf(c_0_94, negated_conjecture, (k6_partfun1(X1)=esk10_0|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.41  fof(c_0_95, plain, ![X21, X22, X23, X25, X26, X27, X29]:((((r2_hidden(esk2_3(X21,X22,X23),k1_relat_1(X21))|~r2_hidden(X23,X22)|X22!=k2_relat_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(X23=k1_funct_1(X21,esk2_3(X21,X22,X23))|~r2_hidden(X23,X22)|X22!=k2_relat_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(~r2_hidden(X26,k1_relat_1(X21))|X25!=k1_funct_1(X21,X26)|r2_hidden(X25,X22)|X22!=k2_relat_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&((~r2_hidden(esk3_2(X21,X27),X27)|(~r2_hidden(X29,k1_relat_1(X21))|esk3_2(X21,X27)!=k1_funct_1(X21,X29))|X27=k2_relat_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&((r2_hidden(esk4_2(X21,X27),k1_relat_1(X21))|r2_hidden(esk3_2(X21,X27),X27)|X27=k2_relat_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(esk3_2(X21,X27)=k1_funct_1(X21,esk4_2(X21,X27))|r2_hidden(esk3_2(X21,X27),X27)|X27=k2_relat_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk8_0,k2_relat_1(esk10_0)))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_28, c_0_55])).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (v1_partfun1(esk10_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.20/0.41  cnf(c_0_98, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk10_0))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_96, c_0_62])).
% 0.20/0.41  cnf(c_0_100, negated_conjecture, (k2_relat_1(esk10_0)=esk10_0), inference(sr,[status(thm)],[c_0_83, c_0_86])).
% 0.20/0.41  cnf(c_0_101, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(esk10_0))), inference(spm,[status(thm)],[c_0_86, c_0_97])).
% 0.20/0.41  cnf(c_0_102, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_21, c_0_40])).
% 0.20/0.41  cnf(c_0_103, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_98])])).
% 0.20/0.41  cnf(c_0_104, negated_conjecture, (~r2_hidden(X1,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100]), c_0_89])])).
% 0.20/0.41  cnf(c_0_105, negated_conjecture, (r2_hidden(esk1_2(esk8_0,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.20/0.41  cnf(c_0_106, negated_conjecture, (~r2_hidden(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_100]), c_0_45]), c_0_46]), c_0_44])]), c_0_104])).
% 0.20/0.41  cnf(c_0_107, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_105, c_0_106]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 108
% 0.20/0.41  # Proof object clause steps            : 81
% 0.20/0.41  # Proof object formula steps           : 27
% 0.20/0.41  # Proof object conjectures             : 39
% 0.20/0.41  # Proof object clause conjectures      : 36
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 22
% 0.20/0.41  # Proof object initial formulas used   : 13
% 0.20/0.41  # Proof object generating inferences   : 45
% 0.20/0.41  # Proof object simplifying inferences  : 52
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 16
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 45
% 0.20/0.41  # Removed in clause preprocessing      : 3
% 0.20/0.41  # Initial clauses in saturation        : 42
% 0.20/0.41  # Processed clauses                    : 549
% 0.20/0.41  # ...of these trivial                  : 32
% 0.20/0.41  # ...subsumed                          : 208
% 0.20/0.41  # ...remaining for further processing  : 309
% 0.20/0.41  # Other redundant clauses eliminated   : 15
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 12
% 0.20/0.41  # Backward-rewritten                   : 47
% 0.20/0.41  # Generated clauses                    : 1085
% 0.20/0.41  # ...of the previous two non-trivial   : 945
% 0.20/0.41  # Contextual simplify-reflections      : 1
% 0.20/0.41  # Paramodulations                      : 1056
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 15
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
% 0.20/0.41  # Current number of processed clauses  : 180
% 0.20/0.41  #    Positive orientable unit clauses  : 27
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 12
% 0.20/0.41  #    Non-unit-clauses                  : 141
% 0.20/0.41  # Current number of unprocessed clauses: 430
% 0.20/0.41  # ...number of literals in the above   : 1443
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 117
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 8111
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 5012
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 147
% 0.20/0.41  # Unit Clause-clause subsumption calls : 1215
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 26
% 0.20/0.41  # BW rewrite match successes           : 18
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 15753
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.063 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.068 s
% 0.20/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
