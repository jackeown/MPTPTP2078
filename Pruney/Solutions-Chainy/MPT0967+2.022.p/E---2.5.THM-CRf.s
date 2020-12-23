%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:24 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 356 expanded)
%              Number of clauses        :   67 ( 161 expanded)
%              Number of leaves         :   19 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  310 (1426 expanded)
%              Number of equality atoms :   85 ( 317 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X2,X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_2])).

fof(c_0_20,plain,(
    ! [X36,X37] :
      ( ~ v1_xboole_0(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | v1_xboole_0(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & r1_tarski(esk6_0,esk7_0)
    & ( esk6_0 != k1_xboole_0
      | esk5_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk8_0)
      | ~ v1_funct_2(esk8_0,esk5_0,esk7_0)
      | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X28,X29] :
      ( ( k2_zfmisc_1(X28,X29) != k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k2_zfmisc_1(X28,X29) = k1_xboole_0 )
      & ( X29 != k1_xboole_0
        | k2_zfmisc_1(X28,X29) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X26,X27] :
      ( ~ v1_xboole_0(X26)
      | X26 = X27
      | ~ v1_xboole_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_26,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_29,plain,(
    ! [X60,X61] :
      ( m1_subset_1(esk4_2(X60,X61),k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      & v1_relat_1(esk4_2(X60,X61))
      & v4_relat_1(esk4_2(X60,X61),X60)
      & v5_relat_1(esk4_2(X60,X61),X61)
      & v1_funct_1(esk4_2(X60,X61))
      & v1_funct_2(esk4_2(X60,X61),X60,X61) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

fof(c_0_30,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_31,plain,(
    ! [X30,X31,X32] :
      ( ( r1_tarski(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))
        | ~ r1_tarski(X30,X31) )
      & ( r1_tarski(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31))
        | ~ r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_32,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r2_hidden(esk3_2(X16,X17),X16)
        | r1_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_2(X16,X17),X17)
        | r1_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_37,plain,(
    ! [X25] :
      ( ( r1_xboole_0(X25,X25)
        | X25 != k1_xboole_0 )
      & ( X25 = k1_xboole_0
        | ~ r1_xboole_0(X25,X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_38,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X40,k1_zfmisc_1(X41))
        | r1_tarski(X40,X41) )
      & ( ~ r1_tarski(X40,X41)
        | m1_subset_1(X40,k1_zfmisc_1(X41)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_39,plain,(
    ! [X42,X43,X44] :
      ( ~ r2_hidden(X42,X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(X44))
      | m1_subset_1(X42,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_funct_1(esk8_0)
    | ~ v1_funct_2(esk8_0,esk5_0,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( X1 = esk8_0
    | esk6_0 != k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_47,plain,
    ( v1_xboole_0(esk4_2(X1,X2))
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_35])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_52,plain,(
    ! [X33,X34] :
      ( ~ r1_tarski(X33,X34)
      | r1_tarski(k1_zfmisc_1(X33),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_53,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X38,X39)
      | v1_xboole_0(X39)
      | r2_hidden(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_54,plain,(
    ! [X35] : ~ v1_xboole_0(k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X4,X3)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_2(esk8_0,esk5_0,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_58,plain,
    ( v1_funct_2(esk4_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( esk4_2(X1,X2) = esk8_0
    | esk6_0 != k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_60,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | r2_hidden(esk2_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(X1,X4))
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_55,c_0_45])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_2(esk8_0,esk5_0,esk7_0)
    | ~ r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_50])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk8_0,X1,X2)
    | esk6_0 != k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_72,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_73,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_23]),c_0_67])).

fof(c_0_77,plain,(
    ! [X57,X58,X59] :
      ( ( ~ v1_funct_2(X59,X57,X58)
        | X57 = k1_relset_1(X57,X58,X59)
        | X58 = k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( X57 != k1_relset_1(X57,X58,X59)
        | v1_funct_2(X59,X57,X58)
        | X58 = k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( ~ v1_funct_2(X59,X57,X58)
        | X57 = k1_relset_1(X57,X58,X59)
        | X57 != k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( X57 != k1_relset_1(X57,X58,X59)
        | v1_funct_2(X59,X57,X58)
        | X57 != k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( ~ v1_funct_2(X59,X57,X58)
        | X59 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 != k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( X59 != k1_xboole_0
        | v1_funct_2(X59,X57,X58)
        | X57 = k1_xboole_0
        | X58 != k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk6_0),X2)
    | r2_hidden(esk2_2(k2_zfmisc_1(X1,esk6_0),X2),k2_zfmisc_1(X1,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_63])).

cnf(c_0_80,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ v1_funct_2(esk8_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(esk8_0,X1,X2)
    | k2_zfmisc_1(X1,X2) != k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_85,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | k1_relset_1(X54,X55,X56) = k1_relat_1(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_86,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk6_0),k2_zfmisc_1(X1,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk7_0) != k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_41])).

cnf(c_0_92,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_23]),c_0_87])])).

cnf(c_0_94,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_95,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_96,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_27]),c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_funct_2(esk8_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_91]),c_0_63])])).

cnf(c_0_100,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_23])])).

cnf(c_0_101,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_94]),c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( k1_relset_1(esk5_0,esk7_0,esk8_0) != esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0 ),
    inference(sr,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_92]),c_0_103]),c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 11.69/11.86  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 11.69/11.86  # and selection function PSelectComplexExceptUniqMaxHorn.
% 11.69/11.86  #
% 11.69/11.86  # Preprocessing time       : 0.029 s
% 11.69/11.86  
% 11.69/11.86  # Proof found!
% 11.69/11.86  # SZS status Theorem
% 11.69/11.86  # SZS output start CNFRefutation
% 11.69/11.86  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 11.69/11.86  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.69/11.86  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.69/11.86  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 11.69/11.86  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.69/11.86  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 11.69/11.86  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.69/11.86  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 11.69/11.86  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.69/11.86  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.69/11.86  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 11.69/11.86  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.69/11.86  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 11.69/11.86  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 11.69/11.86  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 11.69/11.86  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.69/11.86  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.69/11.86  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.69/11.86  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.69/11.86  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 11.69/11.86  fof(c_0_20, plain, ![X36, X37]:(~v1_xboole_0(X36)|(~m1_subset_1(X37,k1_zfmisc_1(X36))|v1_xboole_0(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 11.69/11.86  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r1_tarski(esk6_0,esk7_0)&((esk6_0!=k1_xboole_0|esk5_0=k1_xboole_0)&(~v1_funct_1(esk8_0)|~v1_funct_2(esk8_0,esk5_0,esk7_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 11.69/11.86  cnf(c_0_22, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 11.69/11.86  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 11.69/11.86  fof(c_0_24, plain, ![X28, X29]:((k2_zfmisc_1(X28,X29)!=k1_xboole_0|(X28=k1_xboole_0|X29=k1_xboole_0))&((X28!=k1_xboole_0|k2_zfmisc_1(X28,X29)=k1_xboole_0)&(X29!=k1_xboole_0|k2_zfmisc_1(X28,X29)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 11.69/11.86  fof(c_0_25, plain, ![X26, X27]:(~v1_xboole_0(X26)|X26=X27|~v1_xboole_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 11.69/11.86  cnf(c_0_26, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 11.69/11.86  cnf(c_0_27, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 11.69/11.86  cnf(c_0_28, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 11.69/11.86  fof(c_0_29, plain, ![X60, X61]:(((((m1_subset_1(esk4_2(X60,X61),k1_zfmisc_1(k2_zfmisc_1(X60,X61)))&v1_relat_1(esk4_2(X60,X61)))&v4_relat_1(esk4_2(X60,X61),X60))&v5_relat_1(esk4_2(X60,X61),X61))&v1_funct_1(esk4_2(X60,X61)))&v1_funct_2(esk4_2(X60,X61),X60,X61)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 11.69/11.86  fof(c_0_30, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 11.69/11.86  fof(c_0_31, plain, ![X30, X31, X32]:((r1_tarski(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))|~r1_tarski(X30,X31))&(r1_tarski(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31))|~r1_tarski(X30,X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 11.69/11.86  fof(c_0_32, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 11.69/11.86  cnf(c_0_33, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 11.69/11.86  cnf(c_0_34, negated_conjecture, (v1_xboole_0(esk8_0)|esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 11.69/11.86  cnf(c_0_35, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 11.69/11.86  fof(c_0_36, plain, ![X16, X17, X19, X20, X21]:(((r2_hidden(esk3_2(X16,X17),X16)|r1_xboole_0(X16,X17))&(r2_hidden(esk3_2(X16,X17),X17)|r1_xboole_0(X16,X17)))&(~r2_hidden(X21,X19)|~r2_hidden(X21,X20)|~r1_xboole_0(X19,X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 11.69/11.86  fof(c_0_37, plain, ![X25]:((r1_xboole_0(X25,X25)|X25!=k1_xboole_0)&(X25=k1_xboole_0|~r1_xboole_0(X25,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 11.69/11.86  fof(c_0_38, plain, ![X40, X41]:((~m1_subset_1(X40,k1_zfmisc_1(X41))|r1_tarski(X40,X41))&(~r1_tarski(X40,X41)|m1_subset_1(X40,k1_zfmisc_1(X41)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 11.69/11.86  fof(c_0_39, plain, ![X42, X43, X44]:(~r2_hidden(X42,X43)|~m1_subset_1(X43,k1_zfmisc_1(X44))|m1_subset_1(X42,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 11.69/11.86  cnf(c_0_40, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 11.69/11.86  cnf(c_0_41, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 11.69/11.86  cnf(c_0_42, negated_conjecture, (~v1_funct_1(esk8_0)|~v1_funct_2(esk8_0,esk5_0,esk7_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 11.69/11.86  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 11.69/11.86  cnf(c_0_44, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 11.69/11.86  cnf(c_0_45, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 11.69/11.86  cnf(c_0_46, negated_conjecture, (X1=esk8_0|esk6_0!=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 11.69/11.86  cnf(c_0_47, plain, (v1_xboole_0(esk4_2(X1,X2))|~v1_xboole_0(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_22, c_0_35])).
% 11.69/11.86  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 11.69/11.86  cnf(c_0_49, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 11.69/11.86  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 11.69/11.86  cnf(c_0_51, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 11.69/11.86  fof(c_0_52, plain, ![X33, X34]:(~r1_tarski(X33,X34)|r1_tarski(k1_zfmisc_1(X33),k1_zfmisc_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 11.69/11.86  fof(c_0_53, plain, ![X38, X39]:(~m1_subset_1(X38,X39)|(v1_xboole_0(X39)|r2_hidden(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 11.69/11.86  fof(c_0_54, plain, ![X35]:~v1_xboole_0(k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 11.69/11.86  cnf(c_0_55, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X4,X3)|~r2_hidden(X1,k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 11.69/11.86  cnf(c_0_56, negated_conjecture, (~v1_funct_2(esk8_0,esk5_0,esk7_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 11.69/11.86  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 11.69/11.86  cnf(c_0_58, plain, (v1_funct_2(esk4_2(X1,X2),X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 11.69/11.86  cnf(c_0_59, negated_conjecture, (esk4_2(X1,X2)=esk8_0|esk6_0!=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 11.69/11.86  cnf(c_0_60, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 11.69/11.86  cnf(c_0_61, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 11.69/11.86  cnf(c_0_62, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_22, c_0_50])).
% 11.69/11.86  cnf(c_0_63, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 11.69/11.86  cnf(c_0_64, plain, (m1_subset_1(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 11.69/11.86  cnf(c_0_65, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 11.69/11.86  cnf(c_0_66, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 11.69/11.86  cnf(c_0_67, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 11.69/11.86  cnf(c_0_68, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|r2_hidden(esk2_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(X1,X4))|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_55, c_0_45])).
% 11.69/11.86  cnf(c_0_69, negated_conjecture, (~v1_funct_2(esk8_0,esk5_0,esk7_0)|~r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_56, c_0_50])).
% 11.69/11.86  cnf(c_0_70, negated_conjecture, (r1_tarski(esk8_0,X1)|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_34])).
% 11.69/11.86  cnf(c_0_71, negated_conjecture, (v1_funct_2(esk8_0,X1,X2)|esk6_0!=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 11.69/11.86  cnf(c_0_72, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 11.69/11.86  fof(c_0_73, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 11.69/11.86  cnf(c_0_74, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 11.69/11.86  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X3,X2)|~r2_hidden(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 11.69/11.86  cnf(c_0_76, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_23]), c_0_67])).
% 11.69/11.86  fof(c_0_77, plain, ![X57, X58, X59]:((((~v1_funct_2(X59,X57,X58)|X57=k1_relset_1(X57,X58,X59)|X58=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))&(X57!=k1_relset_1(X57,X58,X59)|v1_funct_2(X59,X57,X58)|X58=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))))&((~v1_funct_2(X59,X57,X58)|X57=k1_relset_1(X57,X58,X59)|X57!=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))&(X57!=k1_relset_1(X57,X58,X59)|v1_funct_2(X59,X57,X58)|X57!=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))))&((~v1_funct_2(X59,X57,X58)|X59=k1_xboole_0|X57=k1_xboole_0|X58!=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))&(X59!=k1_xboole_0|v1_funct_2(X59,X57,X58)|X57=k1_xboole_0|X58!=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 11.69/11.86  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 11.69/11.86  cnf(c_0_79, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,esk6_0),X2)|r2_hidden(esk2_2(k2_zfmisc_1(X1,esk6_0),X2),k2_zfmisc_1(X1,esk7_0))), inference(spm,[status(thm)],[c_0_68, c_0_63])).
% 11.69/11.86  cnf(c_0_80, negated_conjecture, (esk6_0!=k1_xboole_0|~v1_funct_2(esk8_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 11.69/11.86  cnf(c_0_81, negated_conjecture, (v1_funct_2(esk8_0,X1,X2)|k2_zfmisc_1(X1,X2)!=k1_xboole_0|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 11.69/11.86  cnf(c_0_82, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 11.69/11.86  cnf(c_0_83, negated_conjecture, (v1_xboole_0(esk6_0)|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_72])).
% 11.69/11.86  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(X1))|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 11.69/11.86  fof(c_0_85, plain, ![X54, X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|k1_relset_1(X54,X55,X56)=k1_relat_1(X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 11.69/11.86  cnf(c_0_86, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 11.69/11.86  cnf(c_0_87, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 11.69/11.86  cnf(c_0_88, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,esk6_0),k2_zfmisc_1(X1,esk7_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 11.69/11.86  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk5_0,esk7_0)!=k1_xboole_0|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 11.69/11.86  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 11.69/11.86  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_84, c_0_41])).
% 11.69/11.86  cnf(c_0_92, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 11.69/11.86  cnf(c_0_93, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_23]), c_0_87])])).
% 11.69/11.86  cnf(c_0_94, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 11.69/11.86  cnf(c_0_95, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 11.69/11.86  cnf(c_0_96, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 11.69/11.86  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(spm,[status(thm)],[c_0_84, c_0_88])).
% 11.69/11.86  cnf(c_0_98, negated_conjecture, (esk7_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_27]), c_0_90])).
% 11.69/11.86  cnf(c_0_99, negated_conjecture, (~v1_funct_2(esk8_0,esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_91]), c_0_63])])).
% 11.69/11.86  cnf(c_0_100, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_23])])).
% 11.69/11.86  cnf(c_0_101, negated_conjecture, (esk6_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_94]), c_0_95])).
% 11.69/11.86  cnf(c_0_102, negated_conjecture, (k1_relset_1(esk5_0,esk7_0,esk8_0)!=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_99])).
% 11.69/11.86  cnf(c_0_103, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0), inference(sr,[status(thm)],[c_0_100, c_0_101])).
% 11.69/11.86  cnf(c_0_104, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_92]), c_0_103]), c_0_97])]), ['proof']).
% 11.69/11.86  # SZS output end CNFRefutation
% 11.69/11.86  # Proof object total steps             : 105
% 11.69/11.86  # Proof object clause steps            : 67
% 11.69/11.86  # Proof object formula steps           : 38
% 11.69/11.86  # Proof object conjectures             : 37
% 11.69/11.86  # Proof object clause conjectures      : 34
% 11.69/11.86  # Proof object formula conjectures     : 3
% 11.69/11.86  # Proof object initial clauses used    : 30
% 11.69/11.86  # Proof object initial formulas used   : 19
% 11.69/11.86  # Proof object generating inferences   : 35
% 11.69/11.86  # Proof object simplifying inferences  : 19
% 11.69/11.86  # Training examples: 0 positive, 0 negative
% 11.69/11.86  # Parsed axioms                        : 26
% 11.69/11.86  # Removed by relevancy pruning/SinE    : 0
% 11.69/11.86  # Initial clauses                      : 56
% 11.69/11.86  # Removed in clause preprocessing      : 0
% 11.69/11.86  # Initial clauses in saturation        : 56
% 11.69/11.86  # Processed clauses                    : 69835
% 11.69/11.86  # ...of these trivial                  : 1179
% 11.69/11.86  # ...subsumed                          : 63501
% 11.69/11.86  # ...remaining for further processing  : 5155
% 11.69/11.86  # Other redundant clauses eliminated   : 58
% 11.69/11.86  # Clauses deleted for lack of memory   : 0
% 11.69/11.86  # Backward-subsumed                    : 506
% 11.69/11.86  # Backward-rewritten                   : 44
% 11.69/11.86  # Generated clauses                    : 1220047
% 11.69/11.86  # ...of the previous two non-trivial   : 1056575
% 11.69/11.86  # Contextual simplify-reflections      : 234
% 11.69/11.86  # Paramodulations                      : 1219512
% 11.69/11.86  # Factorizations                       : 173
% 11.69/11.86  # Equation resolutions                 : 358
% 11.69/11.86  # Propositional unsat checks           : 0
% 11.69/11.86  #    Propositional check models        : 0
% 11.69/11.86  #    Propositional check unsatisfiable : 0
% 11.69/11.86  #    Propositional clauses             : 0
% 11.69/11.86  #    Propositional clauses after purity: 0
% 11.69/11.86  #    Propositional unsat core size     : 0
% 11.69/11.86  #    Propositional preprocessing time  : 0.000
% 11.69/11.86  #    Propositional encoding time       : 0.000
% 11.69/11.86  #    Propositional solver time         : 0.000
% 11.69/11.86  #    Success case prop preproc time    : 0.000
% 11.69/11.86  #    Success case prop encoding time   : 0.000
% 11.69/11.86  #    Success case prop solver time     : 0.000
% 11.69/11.86  # Current number of processed clauses  : 4599
% 11.69/11.86  #    Positive orientable unit clauses  : 63
% 11.69/11.86  #    Positive unorientable unit clauses: 0
% 11.69/11.86  #    Negative unit clauses             : 31
% 11.69/11.86  #    Non-unit-clauses                  : 4505
% 11.69/11.86  # Current number of unprocessed clauses: 982273
% 11.69/11.86  # ...number of literals in the above   : 4108585
% 11.69/11.86  # Current number of archived formulas  : 0
% 11.69/11.86  # Current number of archived clauses   : 554
% 11.69/11.86  # Clause-clause subsumption calls (NU) : 1484230
% 11.69/11.86  # Rec. Clause-clause subsumption calls : 741201
% 11.69/11.86  # Non-unit clause-clause subsumptions  : 14598
% 11.69/11.86  # Unit Clause-clause subsumption calls : 7171
% 11.69/11.86  # Rewrite failures with RHS unbound    : 0
% 11.69/11.86  # BW rewrite match attempts            : 58
% 11.69/11.86  # BW rewrite match successes           : 28
% 11.69/11.86  # Condensation attempts                : 0
% 11.69/11.86  # Condensation successes               : 0
% 11.69/11.86  # Termbank termtop insertions          : 15763596
% 11.69/11.90  
% 11.69/11.90  # -------------------------------------------------
% 11.69/11.90  # User time                : 11.091 s
% 11.69/11.90  # System time              : 0.463 s
% 11.69/11.90  # Total time               : 11.554 s
% 11.69/11.90  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
