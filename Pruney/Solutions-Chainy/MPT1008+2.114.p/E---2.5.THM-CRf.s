%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 384 expanded)
%              Number of clauses        :   33 ( 139 expanded)
%              Number of leaves         :   16 ( 116 expanded)
%              Depth                    :    9
%              Number of atoms          :  219 ( 726 expanded)
%              Number of equality atoms :  131 ( 483 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

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

fof(t168_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k2_relat_1(k7_relat_1(X2,k1_tarski(X1))) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

fof(c_0_17,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))
    & esk3_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk2_0),esk3_0,esk4_0) != k1_tarski(k1_funct_1(esk4_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_18,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k5_enumset1(X26,X26,X27,X28,X29,X30,X31) = k4_enumset1(X26,X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38] : k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38) = k5_enumset1(X32,X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_25,plain,(
    ! [X67,X68,X69] :
      ( ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | k1_relset_1(X67,X68,X69) = k1_relat_1(X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X70,X71,X72] :
      ( ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | k2_relset_1(X70,X71,X72) = k2_relat_1(X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_35,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58] :
      ( ( ~ r2_hidden(X48,X47)
        | X48 = X39
        | X48 = X40
        | X48 = X41
        | X48 = X42
        | X48 = X43
        | X48 = X44
        | X48 = X45
        | X48 = X46
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X39
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X40
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X41
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X42
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X43
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X44
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X45
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X46
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X50
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X51
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X52
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X53
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X54
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X55
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X56
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X57
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X50
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X51
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X52
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X53
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X54
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X55
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X56
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X57
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

fof(c_0_36,plain,(
    ! [X73,X74,X75] :
      ( ( ~ v1_funct_2(X75,X73,X74)
        | X73 = k1_relset_1(X73,X74,X75)
        | X74 = k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X73 != k1_relset_1(X73,X74,X75)
        | v1_funct_2(X75,X73,X74)
        | X74 = k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( ~ v1_funct_2(X75,X73,X74)
        | X73 = k1_relset_1(X73,X74,X75)
        | X73 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X73 != k1_relset_1(X73,X74,X75)
        | v1_funct_2(X75,X73,X74)
        | X73 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( ~ v1_funct_2(X75,X73,X74)
        | X75 = k1_xboole_0
        | X73 = k1_xboole_0
        | X74 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X75 != k1_xboole_0
        | v1_funct_2(X75,X73,X74)
        | X73 = k1_xboole_0
        | X74 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk2_0),esk3_0,esk4_0) != k1_tarski(k1_funct_1(esk4_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X65,X66] :
      ( ~ v1_relat_1(X66)
      | ~ v1_funct_1(X66)
      | ~ r2_hidden(X65,k1_relat_1(X66))
      | k2_relat_1(k7_relat_1(X66,k1_tarski(X65))) = k1_tarski(k1_funct_1(X66,X65)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_funct_1])])).

fof(c_0_43,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(X60))
      | v1_relat_1(X61) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_44,plain,(
    ! [X62,X63] : v1_relat_1(k2_zfmisc_1(X62,X63)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( k1_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk4_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( k2_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0) != k6_enumset1(k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( k2_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_52,plain,
    ( k2_relat_1(k7_relat_1(X1,k1_tarski(X2))) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_45])])).

cnf(c_0_56,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_relat_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_38]),c_0_47]),c_0_48])]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k6_enumset1(k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0)) != k2_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( k2_relat_1(k7_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) = k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_38]),c_0_54])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_62,plain,(
    ! [X64] :
      ( ~ v1_relat_1(X64)
      | k7_relat_1(X64,k1_relat_1(X64)) = X64 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk4_0,k1_relat_1(esk4_0))) != k2_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_56]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_64,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.39  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.13/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.39  fof(t168_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k2_relat_1(k7_relat_1(X2,k1_tarski(X1)))=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 0.13/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.39  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.13/0.39  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))))&(esk3_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk2_0),esk3_0,esk4_0)!=k1_tarski(k1_funct_1(esk4_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.39  fof(c_0_18, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_19, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_20, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_21, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.39  fof(c_0_22, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.39  fof(c_0_23, plain, ![X26, X27, X28, X29, X30, X31]:k5_enumset1(X26,X26,X27,X28,X29,X30,X31)=k4_enumset1(X26,X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.39  fof(c_0_24, plain, ![X32, X33, X34, X35, X36, X37, X38]:k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38)=k5_enumset1(X32,X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.39  fof(c_0_25, plain, ![X67, X68, X69]:(~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))|k1_relset_1(X67,X68,X69)=k1_relat_1(X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_31, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_32, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_33, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  fof(c_0_34, plain, ![X70, X71, X72]:(~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|k2_relset_1(X70,X71,X72)=k2_relat_1(X72)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.39  fof(c_0_35, plain, ![X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58]:(((~r2_hidden(X48,X47)|(X48=X39|X48=X40|X48=X41|X48=X42|X48=X43|X48=X44|X48=X45|X48=X46)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46))&((((((((X49!=X39|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46))&(X49!=X40|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X41|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X42|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X43|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X44|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X45|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X46|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46))))&(((((((((esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X50|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X51|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X52|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X53|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X54|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X55|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X56|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X57|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X50|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X51|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X52|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X53|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X54|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X55|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X56|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X57)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.13/0.39  fof(c_0_36, plain, ![X73, X74, X75]:((((~v1_funct_2(X75,X73,X74)|X73=k1_relset_1(X73,X74,X75)|X74=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(X73!=k1_relset_1(X73,X74,X75)|v1_funct_2(X75,X73,X74)|X74=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))&((~v1_funct_2(X75,X73,X74)|X73=k1_relset_1(X73,X74,X75)|X73!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(X73!=k1_relset_1(X73,X74,X75)|v1_funct_2(X75,X73,X74)|X73!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))))&((~v1_funct_2(X75,X73,X74)|X75=k1_xboole_0|X73=k1_xboole_0|X74!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(X75!=k1_xboole_0|v1_funct_2(X75,X73,X74)|X73=k1_xboole_0|X74!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.39  cnf(c_0_37, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (k2_relset_1(k1_tarski(esk2_0),esk3_0,esk4_0)!=k1_tarski(k1_funct_1(esk4_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_41, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  fof(c_0_42, plain, ![X65, X66]:(~v1_relat_1(X66)|~v1_funct_1(X66)|(~r2_hidden(X65,k1_relat_1(X66))|k2_relat_1(k7_relat_1(X66,k1_tarski(X65)))=k1_tarski(k1_funct_1(X66,X65)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_funct_1])])).
% 0.13/0.39  fof(c_0_43, plain, ![X60, X61]:(~v1_relat_1(X60)|(~m1_subset_1(X61,k1_zfmisc_1(X60))|v1_relat_1(X61))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.39  fof(c_0_44, plain, ![X62, X63]:v1_relat_1(k2_zfmisc_1(X62,X63)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.39  cnf(c_0_45, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_46, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (k1_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk4_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (k2_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0)!=k6_enumset1(k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (k2_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 0.13/0.39  cnf(c_0_52, plain, (k2_relat_1(k7_relat_1(X1,k1_tarski(X2)))=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_53, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_54, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_55, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_45])])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_relat_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_38]), c_0_47]), c_0_48])]), c_0_49])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (k6_enumset1(k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0))!=k2_relat_1(esk4_0)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.39  cnf(c_0_58, plain, (k2_relat_1(k7_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))=k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_38]), c_0_54])])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.39  fof(c_0_62, plain, ![X64]:(~v1_relat_1(X64)|k7_relat_1(X64,k1_relat_1(X64))=X64), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (k2_relat_1(k7_relat_1(esk4_0,k1_relat_1(esk4_0)))!=k2_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_56]), c_0_59]), c_0_60]), c_0_61])])).
% 0.13/0.39  cnf(c_0_64, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_60])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 66
% 0.13/0.39  # Proof object clause steps            : 33
% 0.13/0.39  # Proof object formula steps           : 33
% 0.13/0.39  # Proof object conjectures             : 19
% 0.13/0.39  # Proof object clause conjectures      : 16
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 20
% 0.13/0.39  # Proof object initial formulas used   : 16
% 0.13/0.39  # Proof object generating inferences   : 7
% 0.13/0.39  # Proof object simplifying inferences  : 58
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 16
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 42
% 0.13/0.39  # Removed in clause preprocessing      : 7
% 0.13/0.39  # Initial clauses in saturation        : 35
% 0.13/0.39  # Processed clauses                    : 96
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 94
% 0.13/0.39  # Other redundant clauses eliminated   : 22
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 4
% 0.13/0.39  # Generated clauses                    : 45
% 0.13/0.39  # ...of the previous two non-trivial   : 37
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 32
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 22
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 42
% 0.13/0.39  #    Positive orientable unit clauses  : 17
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 22
% 0.13/0.39  # Current number of unprocessed clauses: 11
% 0.13/0.39  # ...number of literals in the above   : 54
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 46
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 380
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 254
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 1
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 57
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 3422
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.033 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.037 s
% 0.13/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
