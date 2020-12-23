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
% DateTime   : Thu Dec  3 11:07:13 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  124 (13271 expanded)
%              Number of clauses        :   84 (6206 expanded)
%              Number of leaves         :   20 (3323 expanded)
%              Depth                    :   18
%              Number of atoms          :  312 (29274 expanded)
%              Number of equality atoms :  128 (10209 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t169_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( k1_relat_1(X3) = X1
          & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(t121_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(t160_funct_2,axiom,(
    ! [X1,X2] : k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(fc3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2) )
     => v1_xboole_0(k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

fof(c_0_21,plain,(
    ! [X34,X35,X36] :
      ( ( v1_funct_1(X36)
        | ~ r2_hidden(X36,k1_funct_2(X34,X35)) )
      & ( v1_funct_2(X36,X34,X35)
        | ~ r2_hidden(X36,k1_funct_2(X34,X35)) )
      & ( m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ r2_hidden(X36,k1_funct_2(X34,X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).

fof(c_0_22,plain,(
    ! [X37,X38] : k5_partfun1(X37,X38,k3_partfun1(k1_xboole_0,X37,X38)) = k1_funct_2(X37,X38) ),
    inference(variable_rename,[status(thm)],[t160_funct_2])).

fof(c_0_23,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_24,plain,(
    v1_xboole_0(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0))
    & ( k1_relat_1(esk5_0) != esk3_0
      | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X25] :
      ( ( k1_relat_1(X25) != k1_xboole_0
        | k2_relat_1(X25) = k1_xboole_0
        | ~ v1_relat_1(X25) )
      & ( k2_relat_1(X25) != k1_xboole_0
        | k1_relat_1(X25) = k1_xboole_0
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_33,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v1_funct_2(X31,X29,X30)
        | X29 = k1_relset_1(X29,X30,X31)
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X29 != k1_relset_1(X29,X30,X31)
        | v1_funct_2(X31,X29,X30)
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ v1_funct_2(X31,X29,X30)
        | X29 = k1_relset_1(X29,X30,X31)
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X29 != k1_relset_1(X29,X30,X31)
        | v1_funct_2(X31,X29,X30)
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ v1_funct_2(X31,X29,X30)
        | X31 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X31 != k1_xboole_0
        | v1_funct_2(X31,X29,X30)
        | X29 = k1_xboole_0
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk5_0,k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_37,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_38,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_40,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(esk2_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_0,k5_partfun1(esk3_0,esk4_0,k3_partfun1(esk2_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_43,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(esk2_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_35])).

fof(c_0_44,plain,(
    ! [X21,X22] :
      ( ( k1_relat_1(k2_zfmisc_1(X21,X22)) = X21
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X21,X22)) = X22
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk5_0) != esk3_0
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,plain,
    ( k2_relat_1(X1) = esk2_0
    | k1_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_35]),c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k1_relset_1(X26,X27,X28) = k1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_50,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | X2 = esk2_0
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

fof(c_0_53,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(k1_relat_1(X23),k1_relat_1(X24))
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r1_tarski(k2_relat_1(X23),k2_relat_1(X24))
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_54,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_55,plain,(
    ! [X19,X20] : v1_relat_1(k2_zfmisc_1(X19,X20)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_56,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(esk5_0) != esk3_0
    | k1_relat_1(esk5_0) != esk2_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_58,plain,
    ( r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_35])).

cnf(c_0_59,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = esk3_0
    | esk2_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

fof(c_0_61,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_62,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_63,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_64,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X2 = esk2_0
    | X1 = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_35]),c_0_35])).

cnf(c_0_66,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( k1_relat_1(esk5_0) != esk3_0
    | k1_relat_1(esk5_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_69,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk2_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_51])])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_72,plain,(
    ! [X18] :
      ( ~ v1_xboole_0(X18)
      | v1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( X1 = esk2_0
    | X2 = esk2_0
    | r1_tarski(k2_relat_1(X3),X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51])).

cnf(c_0_76,negated_conjecture,
    ( esk2_0 = esk4_0
    | esk2_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,esk2_0) = X1 ),
    inference(rw,[status(thm)],[c_0_70,c_0_35])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,X2) = esk2_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_71,c_0_35])).

cnf(c_0_79,plain,
    ( r1_tarski(k2_relat_1(X1),esk2_0)
    | k1_relat_1(X2) != esk2_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_46])).

cnf(c_0_80,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_81,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( esk2_0 = esk4_0
    | r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_47])]),c_0_76])).

cnf(c_0_84,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_85,plain,
    ( esk2_0 = X1
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),esk2_0)
    | k1_relat_1(k2_zfmisc_1(esk3_0,esk4_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_75]),c_0_66]),c_0_47])])).

cnf(c_0_87,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_88,plain,
    ( k1_relat_1(esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_35]),c_0_35])).

cnf(c_0_89,plain,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_29])).

fof(c_0_90,plain,(
    ! [X32,X33] :
      ( v1_xboole_0(X32)
      | ~ v1_xboole_0(X33)
      | v1_xboole_0(k1_funct_2(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).

cnf(c_0_91,plain,
    ( k2_zfmisc_1(X1,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_35]),c_0_35])).

cnf(c_0_92,negated_conjecture,
    ( esk2_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_83]),c_0_69])).

cnf(c_0_93,plain,
    ( k1_relat_1(X1) = esk2_0
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_35]),c_0_35])).

cnf(c_0_94,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk2_0
    | k1_relat_1(k2_zfmisc_1(esk3_0,esk4_0)) != esk2_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_95,plain,
    ( r1_tarski(k1_relat_1(X1),esk2_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])])).

cnf(c_0_96,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k1_funct_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_97,plain,
    ( k2_zfmisc_1(X1,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92]),c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0
    | k1_relat_1(k2_zfmisc_1(esk3_0,esk4_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_47])])).

cnf(c_0_99,plain,
    ( k1_relat_1(X1) = esk2_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_95])).

fof(c_0_100,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_101,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[c_0_96,c_0_27])).

cnf(c_0_102,plain,
    ( esk4_0 = X1
    | ~ r1_tarski(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_92]),c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_66])])).

cnf(c_0_105,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_106,plain,
    ( v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(esk2_0,X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[c_0_101,c_0_35])).

cnf(c_0_107,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_108,plain,
    ( v1_xboole_0(esk4_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_92])).

cnf(c_0_109,negated_conjecture,
    ( esk2_0 != esk3_0
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_104])).

cnf(c_0_110,plain,
    ( X1 = esk2_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk3_0,esk4_0,k3_partfun1(esk2_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_42])).

cnf(c_0_112,plain,
    ( v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(esk5_0,X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_92]),c_0_107])).

cnf(c_0_113,plain,
    ( v1_xboole_0(esk5_0) ),
    inference(rw,[status(thm)],[c_0_108,c_0_107])).

cnf(c_0_114,negated_conjecture,
    ( esk4_0 != esk3_0
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_92]),c_0_92])).

cnf(c_0_115,plain,
    ( r1_tarski(esk4_0,X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_92])).

cnf(c_0_116,plain,
    ( X1 = esk4_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_110,c_0_92])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk3_0,esk5_0,k3_partfun1(esk5_0,esk3_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_92]),c_0_107]),c_0_107]),c_0_107])).

cnf(c_0_118,plain,
    ( v1_xboole_0(k5_partfun1(X1,esk5_0,k3_partfun1(esk5_0,X1,esk5_0)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( esk4_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_97]),c_0_115])])).

cnf(c_0_120,plain,
    ( X1 = esk5_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_116,c_0_107])).

cnf(c_0_121,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(rw,[status(thm)],[c_0_119,c_0_107])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:58:04 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.17/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.17/0.38  #
% 0.17/0.38  # Preprocessing time       : 0.028 s
% 0.17/0.38  # Presaturation interreduction done
% 0.17/0.38  
% 0.17/0.38  # Proof found!
% 0.17/0.38  # SZS status Theorem
% 0.17/0.38  # SZS output start CNFRefutation
% 0.17/0.38  fof(t169_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 0.17/0.38  fof(t121_funct_2, axiom, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 0.17/0.38  fof(t160_funct_2, axiom, ![X1, X2]:k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_funct_2)).
% 0.17/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.17/0.39  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.17/0.39  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.17/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.17/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.17/0.39  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 0.17/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.17/0.39  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.17/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.17/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.17/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.17/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.17/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.17/0.39  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.17/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.17/0.39  fof(fc3_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_xboole_0(X2))=>v1_xboole_0(k1_funct_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 0.17/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.17/0.39  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2))))), inference(assume_negation,[status(cth)],[t169_funct_2])).
% 0.17/0.39  fof(c_0_21, plain, ![X34, X35, X36]:(((v1_funct_1(X36)|~r2_hidden(X36,k1_funct_2(X34,X35)))&(v1_funct_2(X36,X34,X35)|~r2_hidden(X36,k1_funct_2(X34,X35))))&(m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~r2_hidden(X36,k1_funct_2(X34,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).
% 0.17/0.39  fof(c_0_22, plain, ![X37, X38]:k5_partfun1(X37,X38,k3_partfun1(k1_xboole_0,X37,X38))=k1_funct_2(X37,X38), inference(variable_rename,[status(thm)],[t160_funct_2])).
% 0.17/0.39  fof(c_0_23, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.17/0.39  fof(c_0_24, plain, v1_xboole_0(esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.17/0.39  fof(c_0_25, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0))&(k1_relat_1(esk5_0)!=esk3_0|~r1_tarski(k2_relat_1(esk5_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.17/0.39  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.39  cnf(c_0_27, plain, (k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.39  cnf(c_0_28, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.39  cnf(c_0_29, plain, (v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.39  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.39  cnf(c_0_31, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.39  fof(c_0_32, plain, ![X25]:((k1_relat_1(X25)!=k1_xboole_0|k2_relat_1(X25)=k1_xboole_0|~v1_relat_1(X25))&(k2_relat_1(X25)!=k1_xboole_0|k1_relat_1(X25)=k1_xboole_0|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.17/0.39  fof(c_0_33, plain, ![X29, X30, X31]:((((~v1_funct_2(X31,X29,X30)|X29=k1_relset_1(X29,X30,X31)|X30=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X29!=k1_relset_1(X29,X30,X31)|v1_funct_2(X31,X29,X30)|X30=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&((~v1_funct_2(X31,X29,X30)|X29=k1_relset_1(X29,X30,X31)|X29!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X29!=k1_relset_1(X29,X30,X31)|v1_funct_2(X31,X29,X30)|X29!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))))&((~v1_funct_2(X31,X29,X30)|X31=k1_xboole_0|X29=k1_xboole_0|X30!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X31!=k1_xboole_0|v1_funct_2(X31,X29,X30)|X29=k1_xboole_0|X30!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.17/0.39  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.17/0.39  cnf(c_0_35, plain, (k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.17/0.39  cnf(c_0_36, negated_conjecture, (r2_hidden(esk5_0,k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_30, c_0_27])).
% 0.17/0.39  cnf(c_0_37, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_31, c_0_27])).
% 0.17/0.39  cnf(c_0_38, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.17/0.39  fof(c_0_39, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.17/0.39  cnf(c_0_40, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.17/0.39  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(esk2_0,X2,X3)))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.17/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk5_0,k5_partfun1(esk3_0,esk4_0,k3_partfun1(esk2_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_36, c_0_35])).
% 0.17/0.39  cnf(c_0_43, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(esk2_0,X2,X3)))), inference(rw,[status(thm)],[c_0_37, c_0_35])).
% 0.17/0.39  fof(c_0_44, plain, ![X21, X22]:((k1_relat_1(k2_zfmisc_1(X21,X22))=X21|(X21=k1_xboole_0|X22=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X21,X22))=X22|(X21=k1_xboole_0|X22=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.17/0.39  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk5_0)!=esk3_0|~r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.39  cnf(c_0_46, plain, (k2_relat_1(X1)=esk2_0|k1_relat_1(X1)!=esk2_0|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_35]), c_0_35])).
% 0.17/0.39  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.39  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.17/0.39  fof(c_0_49, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k1_relset_1(X26,X27,X28)=k1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.17/0.39  cnf(c_0_50, plain, (k1_relset_1(X1,X2,X3)=X1|X2=esk2_0|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[c_0_40, c_0_35])).
% 0.17/0.39  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.17/0.39  cnf(c_0_52, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.17/0.39  fof(c_0_53, plain, ![X23, X24]:((r1_tarski(k1_relat_1(X23),k1_relat_1(X24))|~r1_tarski(X23,X24)|~v1_relat_1(X24)|~v1_relat_1(X23))&(r1_tarski(k2_relat_1(X23),k2_relat_1(X24))|~r1_tarski(X23,X24)|~v1_relat_1(X24)|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.17/0.39  cnf(c_0_54, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.17/0.39  fof(c_0_55, plain, ![X19, X20]:v1_relat_1(k2_zfmisc_1(X19,X20)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.17/0.39  fof(c_0_56, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.17/0.39  cnf(c_0_57, negated_conjecture, (k1_relat_1(esk5_0)!=esk3_0|k1_relat_1(esk5_0)!=esk2_0|~r1_tarski(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.17/0.39  cnf(c_0_58, plain, (r1_tarski(esk2_0,X1)), inference(rw,[status(thm)],[c_0_48, c_0_35])).
% 0.17/0.39  cnf(c_0_59, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.39  cnf(c_0_60, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=esk3_0|esk2_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.17/0.39  fof(c_0_61, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.17/0.39  fof(c_0_62, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.17/0.39  fof(c_0_63, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.17/0.39  cnf(c_0_64, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.17/0.39  cnf(c_0_65, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X2=esk2_0|X1=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_35]), c_0_35])).
% 0.17/0.39  cnf(c_0_66, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.17/0.39  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.17/0.39  cnf(c_0_68, negated_conjecture, (k1_relat_1(esk5_0)!=esk3_0|k1_relat_1(esk5_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.17/0.39  cnf(c_0_69, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk2_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_51])])).
% 0.17/0.39  cnf(c_0_70, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.17/0.39  cnf(c_0_71, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.17/0.39  fof(c_0_72, plain, ![X18]:(~v1_xboole_0(X18)|v1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.17/0.39  cnf(c_0_73, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.17/0.39  cnf(c_0_74, plain, (X1=esk2_0|X2=esk2_0|r1_tarski(k2_relat_1(X3),X2)|~v1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.17/0.39  cnf(c_0_75, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_51])).
% 0.17/0.39  cnf(c_0_76, negated_conjecture, (esk2_0=esk4_0|esk2_0!=esk3_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.17/0.39  cnf(c_0_77, plain, (k4_xboole_0(X1,esk2_0)=X1), inference(rw,[status(thm)],[c_0_70, c_0_35])).
% 0.17/0.39  cnf(c_0_78, plain, (k4_xboole_0(X1,X2)=esk2_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_71, c_0_35])).
% 0.17/0.39  cnf(c_0_79, plain, (r1_tarski(k2_relat_1(X1),esk2_0)|k1_relat_1(X2)!=esk2_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_64, c_0_46])).
% 0.17/0.39  cnf(c_0_80, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.17/0.39  cnf(c_0_81, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.17/0.39  cnf(c_0_82, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_73])).
% 0.17/0.39  cnf(c_0_83, negated_conjecture, (esk2_0=esk4_0|r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_47])]), c_0_76])).
% 0.17/0.39  cnf(c_0_84, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.17/0.39  cnf(c_0_85, plain, (esk2_0=X1|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.17/0.39  cnf(c_0_86, negated_conjecture, (r1_tarski(k2_relat_1(esk5_0),esk2_0)|k1_relat_1(k2_zfmisc_1(esk3_0,esk4_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_75]), c_0_66]), c_0_47])])).
% 0.17/0.39  cnf(c_0_87, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.17/0.39  cnf(c_0_88, plain, (k1_relat_1(esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_35]), c_0_35])).
% 0.17/0.39  cnf(c_0_89, plain, (v1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_81, c_0_29])).
% 0.17/0.39  fof(c_0_90, plain, ![X32, X33]:(v1_xboole_0(X32)|~v1_xboole_0(X33)|v1_xboole_0(k1_funct_2(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).
% 0.17/0.39  cnf(c_0_91, plain, (k2_zfmisc_1(X1,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_35]), c_0_35])).
% 0.17/0.39  cnf(c_0_92, negated_conjecture, (esk2_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_83]), c_0_69])).
% 0.17/0.39  cnf(c_0_93, plain, (k1_relat_1(X1)=esk2_0|k2_relat_1(X1)!=esk2_0|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_35]), c_0_35])).
% 0.17/0.39  cnf(c_0_94, negated_conjecture, (k2_relat_1(esk5_0)=esk2_0|k1_relat_1(k2_zfmisc_1(esk3_0,esk4_0))!=esk2_0), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.17/0.39  cnf(c_0_95, plain, (r1_tarski(k1_relat_1(X1),esk2_0)|~v1_relat_1(X1)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])])).
% 0.17/0.39  cnf(c_0_96, plain, (v1_xboole_0(X1)|v1_xboole_0(k1_funct_2(X1,X2))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.17/0.39  cnf(c_0_97, plain, (k2_zfmisc_1(X1,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92]), c_0_92])).
% 0.17/0.39  cnf(c_0_98, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0|k1_relat_1(k2_zfmisc_1(esk3_0,esk4_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_47])])).
% 0.17/0.39  cnf(c_0_99, plain, (k1_relat_1(X1)=esk2_0|~v1_relat_1(X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_85, c_0_95])).
% 0.17/0.39  fof(c_0_100, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.17/0.39  cnf(c_0_101, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))|~v1_xboole_0(X2)), inference(rw,[status(thm)],[c_0_96, c_0_27])).
% 0.17/0.39  cnf(c_0_102, plain, (esk4_0=X1|~r1_tarski(X1,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_92]), c_0_92])).
% 0.17/0.39  cnf(c_0_103, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_75, c_0_97])).
% 0.17/0.39  cnf(c_0_104, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_66])])).
% 0.17/0.39  cnf(c_0_105, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.17/0.39  cnf(c_0_106, plain, (v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(esk2_0,X1,X2)))|v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(rw,[status(thm)],[c_0_101, c_0_35])).
% 0.17/0.39  cnf(c_0_107, negated_conjecture, (esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.17/0.39  cnf(c_0_108, plain, (v1_xboole_0(esk4_0)), inference(rw,[status(thm)],[c_0_29, c_0_92])).
% 0.17/0.39  cnf(c_0_109, negated_conjecture, (esk2_0!=esk3_0|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_68, c_0_104])).
% 0.17/0.39  cnf(c_0_110, plain, (X1=esk2_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_28, c_0_35])).
% 0.17/0.39  cnf(c_0_111, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk3_0,esk4_0,k3_partfun1(esk2_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_105, c_0_42])).
% 0.17/0.39  cnf(c_0_112, plain, (v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(esk5_0,X1,X2)))|v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_92]), c_0_107])).
% 0.17/0.39  cnf(c_0_113, plain, (v1_xboole_0(esk5_0)), inference(rw,[status(thm)],[c_0_108, c_0_107])).
% 0.17/0.39  cnf(c_0_114, negated_conjecture, (esk4_0!=esk3_0|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_92]), c_0_92])).
% 0.17/0.39  cnf(c_0_115, plain, (r1_tarski(esk4_0,X1)), inference(rw,[status(thm)],[c_0_58, c_0_92])).
% 0.17/0.39  cnf(c_0_116, plain, (X1=esk4_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_110, c_0_92])).
% 0.17/0.39  cnf(c_0_117, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk3_0,esk5_0,k3_partfun1(esk5_0,esk3_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_92]), c_0_107]), c_0_107]), c_0_107])).
% 0.17/0.39  cnf(c_0_118, plain, (v1_xboole_0(k5_partfun1(X1,esk5_0,k3_partfun1(esk5_0,X1,esk5_0)))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.17/0.39  cnf(c_0_119, negated_conjecture, (esk4_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_97]), c_0_115])])).
% 0.17/0.39  cnf(c_0_120, plain, (X1=esk5_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_116, c_0_107])).
% 0.17/0.39  cnf(c_0_121, negated_conjecture, (v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.17/0.39  cnf(c_0_122, negated_conjecture, (esk3_0!=esk5_0), inference(rw,[status(thm)],[c_0_119, c_0_107])).
% 0.17/0.39  cnf(c_0_123, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122]), ['proof']).
% 0.17/0.39  # SZS output end CNFRefutation
% 0.17/0.39  # Proof object total steps             : 124
% 0.17/0.39  # Proof object clause steps            : 84
% 0.17/0.39  # Proof object formula steps           : 40
% 0.17/0.39  # Proof object conjectures             : 32
% 0.17/0.39  # Proof object clause conjectures      : 29
% 0.17/0.39  # Proof object formula conjectures     : 3
% 0.17/0.39  # Proof object initial clauses used    : 25
% 0.17/0.39  # Proof object initial formulas used   : 20
% 0.17/0.39  # Proof object generating inferences   : 26
% 0.17/0.39  # Proof object simplifying inferences  : 70
% 0.17/0.39  # Training examples: 0 positive, 0 negative
% 0.17/0.39  # Parsed axioms                        : 20
% 0.17/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.39  # Initial clauses                      : 39
% 0.17/0.39  # Removed in clause preprocessing      : 1
% 0.17/0.39  # Initial clauses in saturation        : 38
% 0.17/0.39  # Processed clauses                    : 343
% 0.17/0.39  # ...of these trivial                  : 22
% 0.17/0.39  # ...subsumed                          : 66
% 0.17/0.39  # ...remaining for further processing  : 255
% 0.17/0.39  # Other redundant clauses eliminated   : 11
% 0.17/0.39  # Clauses deleted for lack of memory   : 0
% 0.17/0.39  # Backward-subsumed                    : 4
% 0.17/0.39  # Backward-rewritten                   : 139
% 0.17/0.39  # Generated clauses                    : 771
% 0.17/0.39  # ...of the previous two non-trivial   : 404
% 0.17/0.39  # Contextual simplify-reflections      : 6
% 0.17/0.39  # Paramodulations                      : 761
% 0.17/0.39  # Factorizations                       : 0
% 0.17/0.39  # Equation resolutions                 : 11
% 0.17/0.39  # Propositional unsat checks           : 0
% 0.17/0.39  #    Propositional check models        : 0
% 0.17/0.39  #    Propositional check unsatisfiable : 0
% 0.17/0.39  #    Propositional clauses             : 0
% 0.17/0.39  #    Propositional clauses after purity: 0
% 0.17/0.39  #    Propositional unsat core size     : 0
% 0.17/0.39  #    Propositional preprocessing time  : 0.000
% 0.17/0.39  #    Propositional encoding time       : 0.000
% 0.17/0.39  #    Propositional solver time         : 0.000
% 0.17/0.39  #    Success case prop preproc time    : 0.000
% 0.17/0.39  #    Success case prop encoding time   : 0.000
% 0.17/0.39  #    Success case prop solver time     : 0.000
% 0.17/0.39  # Current number of processed clauses  : 68
% 0.17/0.39  #    Positive orientable unit clauses  : 18
% 0.17/0.39  #    Positive unorientable unit clauses: 0
% 0.17/0.39  #    Negative unit clauses             : 2
% 0.17/0.39  #    Non-unit-clauses                  : 48
% 0.17/0.39  # Current number of unprocessed clauses: 130
% 0.17/0.39  # ...number of literals in the above   : 697
% 0.17/0.39  # Current number of archived formulas  : 0
% 0.17/0.39  # Current number of archived clauses   : 182
% 0.17/0.39  # Clause-clause subsumption calls (NU) : 5689
% 0.17/0.39  # Rec. Clause-clause subsumption calls : 1720
% 0.17/0.39  # Non-unit clause-clause subsumptions  : 69
% 0.17/0.39  # Unit Clause-clause subsumption calls : 13
% 0.17/0.39  # Rewrite failures with RHS unbound    : 0
% 0.17/0.39  # BW rewrite match attempts            : 10
% 0.17/0.39  # BW rewrite match successes           : 9
% 0.17/0.39  # Condensation attempts                : 0
% 0.17/0.39  # Condensation successes               : 0
% 0.17/0.39  # Termbank termtop insertions          : 20079
% 0.17/0.39  
% 0.17/0.39  # -------------------------------------------------
% 0.17/0.39  # User time                : 0.057 s
% 0.17/0.39  # System time              : 0.007 s
% 0.17/0.39  # Total time               : 0.064 s
% 0.17/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
