%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:19 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 497 expanded)
%              Number of clauses        :   47 ( 186 expanded)
%              Number of leaves         :   22 ( 147 expanded)
%              Depth                    :   15
%              Number of atoms          :  241 ( 964 expanded)
%              Number of equality atoms :   74 ( 488 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

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

fof(t15_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t91_mcart_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
            & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

fof(t6_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6,X7] :
                  ( ( r2_hidden(X3,X4)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X6,X7)
                    & r2_hidden(X7,X2) )
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(fc4_subset_1,axiom,(
    ! [X1,X2,X3,X4,X5] : ~ v1_xboole_0(k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_subset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))
    & esk4_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_24,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_25,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | k1_relset_1(X60,X61,X62) = k1_relat_1(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X63,X64,X65,X66] :
      ( ( k1_mcart_1(X63) = X64
        | k1_mcart_1(X63) = X65
        | ~ r2_hidden(X63,k2_zfmisc_1(k2_tarski(X64,X65),X66)) )
      & ( r2_hidden(k2_mcart_1(X63),X66)
        | ~ r2_hidden(X63,k2_zfmisc_1(k2_tarski(X64,X65),X66)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_mcart_1])])])).

fof(c_0_41,plain,(
    ! [X76,X77,X78] :
      ( ( ~ v1_funct_2(X78,X76,X77)
        | X76 = k1_relset_1(X76,X77,X78)
        | X77 = k1_xboole_0
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( X76 != k1_relset_1(X76,X77,X78)
        | v1_funct_2(X78,X76,X77)
        | X77 = k1_xboole_0
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( ~ v1_funct_2(X78,X76,X77)
        | X76 = k1_relset_1(X76,X77,X78)
        | X76 != k1_xboole_0
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( X76 != k1_relset_1(X76,X77,X78)
        | v1_funct_2(X78,X76,X77)
        | X76 != k1_xboole_0
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( ~ v1_funct_2(X78,X76,X77)
        | X78 = k1_xboole_0
        | X76 = k1_xboole_0
        | X77 != k1_xboole_0
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( X78 != k1_xboole_0
        | v1_funct_2(X78,X76,X77)
        | X76 = k1_xboole_0
        | X77 != k1_xboole_0
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_42,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_45,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(X47))
      | ~ r2_hidden(X49,X48)
      | r2_hidden(X49,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_46,plain,
    ( k1_mcart_1(X1) = X2
    | k1_mcart_1(X1) = X3
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k1_mcart_1(X1) = X3
    | k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_relat_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_43])).

fof(c_0_55,plain,(
    ! [X74,X75] :
      ( ( r2_hidden(k1_mcart_1(X75),k1_relat_1(X74))
        | ~ r2_hidden(X75,X74)
        | ~ v1_relat_1(X74) )
      & ( r2_hidden(k2_mcart_1(X75),k2_relat_1(X74))
        | ~ r2_hidden(X75,X74)
        | ~ v1_relat_1(X74) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_mcart_1])])])])).

cnf(c_0_56,negated_conjecture,
    ( k1_mcart_1(X1) = esk3_0
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_58,plain,
    ( r2_hidden(k1_mcart_1(X1),k1_relat_1(X2))
    | ~ r2_hidden(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k1_mcart_1(X1) = esk3_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_60,plain,(
    ! [X67,X69,X70,X71,X72,X73] :
      ( ( r2_hidden(esk2_1(X67),X67)
        | X67 = k1_xboole_0 )
      & ( ~ r2_hidden(X69,X70)
        | ~ r2_hidden(X70,X71)
        | ~ r2_hidden(X71,X72)
        | ~ r2_hidden(X72,X73)
        | ~ r2_hidden(X73,esk2_1(X67))
        | r1_xboole_0(X69,X67)
        | X67 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

fof(c_0_61,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | v1_relat_1(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_62,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_63,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | ~ v1_funct_1(X53)
      | ~ r2_hidden(X52,k1_relat_1(X53))
      | r2_hidden(k1_funct_1(X53,X52),k2_relat_1(X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_43])).

fof(c_0_71,plain,(
    ! [X42,X43,X44,X45,X46] : ~ v1_xboole_0(k3_enumset1(X42,X43,X44,X45,X46)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_subset_1])])).

cnf(c_0_72,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_70])])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_75,plain,(
    ! [X50,X51] :
      ( ( ~ v5_relat_1(X51,X50)
        | r1_tarski(k2_relat_1(X51),X50)
        | ~ v1_relat_1(X51) )
      & ( ~ r1_tarski(k2_relat_1(X51),X50)
        | v5_relat_1(X51,X50)
        | ~ v1_relat_1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_76,plain,(
    ! [X57,X58,X59] :
      ( ( v4_relat_1(X59,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( v5_relat_1(X59,X58)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_77,plain,
    ( ~ v1_xboole_0(k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk5_0,esk3_0),X1)
    | ~ r1_tarski(k2_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_70])])).

cnf(c_0_79,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( ~ v1_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_82,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk5_0,esk3_0),X1)
    | ~ v5_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_70])])).

cnf(c_0_83,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_43])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_53])).

cnf(c_0_86,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_87,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_88,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.026 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 0.12/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.12/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.39  fof(t15_mcart_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 0.12/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.12/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.12/0.39  fof(t91_mcart_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r2_hidden(X2,X1)=>(r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))&r2_hidden(k2_mcart_1(X2),k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_mcart_1)).
% 0.12/0.39  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.12/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.39  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 0.12/0.39  fof(fc4_subset_1, axiom, ![X1, X2, X3, X4, X5]:~(v1_xboole_0(k3_enumset1(X1,X2,X3,X4,X5))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_subset_1)).
% 0.12/0.39  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.12/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.12/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.39  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.12/0.39  fof(c_0_23, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))))&(esk4_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.12/0.39  fof(c_0_24, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.39  fof(c_0_25, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.39  fof(c_0_26, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.39  fof(c_0_27, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.39  fof(c_0_28, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.39  fof(c_0_29, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.39  fof(c_0_30, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.12/0.39  fof(c_0_31, plain, ![X60, X61, X62]:(~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|k1_relset_1(X60,X61,X62)=k1_relat_1(X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.39  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.39  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.39  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.39  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.39  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.39  fof(c_0_40, plain, ![X63, X64, X65, X66]:((k1_mcart_1(X63)=X64|k1_mcart_1(X63)=X65|~r2_hidden(X63,k2_zfmisc_1(k2_tarski(X64,X65),X66)))&(r2_hidden(k2_mcart_1(X63),X66)|~r2_hidden(X63,k2_zfmisc_1(k2_tarski(X64,X65),X66)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_mcart_1])])])).
% 0.12/0.39  fof(c_0_41, plain, ![X76, X77, X78]:((((~v1_funct_2(X78,X76,X77)|X76=k1_relset_1(X76,X77,X78)|X77=k1_xboole_0|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))&(X76!=k1_relset_1(X76,X77,X78)|v1_funct_2(X78,X76,X77)|X77=k1_xboole_0|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))))&((~v1_funct_2(X78,X76,X77)|X76=k1_relset_1(X76,X77,X78)|X76!=k1_xboole_0|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))&(X76!=k1_relset_1(X76,X77,X78)|v1_funct_2(X78,X76,X77)|X76!=k1_xboole_0|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))))&((~v1_funct_2(X78,X76,X77)|X78=k1_xboole_0|X76=k1_xboole_0|X77!=k1_xboole_0|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))&(X78!=k1_xboole_0|v1_funct_2(X78,X76,X77)|X76=k1_xboole_0|X77!=k1_xboole_0|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.12/0.39  cnf(c_0_42, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  fof(c_0_45, plain, ![X47, X48, X49]:(~m1_subset_1(X48,k1_zfmisc_1(X47))|(~r2_hidden(X49,X48)|r2_hidden(X49,X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.12/0.39  cnf(c_0_46, plain, (k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3|~r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.39  cnf(c_0_47, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (k1_relset_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, (v1_funct_2(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.12/0.39  cnf(c_0_50, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  cnf(c_0_51, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.39  cnf(c_0_52, plain, (k1_mcart_1(X1)=X3|k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.12/0.39  cnf(c_0_53, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_relat_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_48]), c_0_49])]), c_0_50])).
% 0.12/0.39  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_43])).
% 0.12/0.39  fof(c_0_55, plain, ![X74, X75]:((r2_hidden(k1_mcart_1(X75),k1_relat_1(X74))|~r2_hidden(X75,X74)|~v1_relat_1(X74))&(r2_hidden(k2_mcart_1(X75),k2_relat_1(X74))|~r2_hidden(X75,X74)|~v1_relat_1(X74))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_mcart_1])])])])).
% 0.12/0.39  cnf(c_0_56, negated_conjecture, (k1_mcart_1(X1)=esk3_0|~r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),X2))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.39  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[c_0_54, c_0_53])).
% 0.12/0.39  cnf(c_0_58, plain, (r2_hidden(k1_mcart_1(X1),k1_relat_1(X2))|~r2_hidden(X1,X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.39  cnf(c_0_59, negated_conjecture, (k1_mcart_1(X1)=esk3_0|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.39  fof(c_0_60, plain, ![X67, X69, X70, X71, X72, X73]:((r2_hidden(esk2_1(X67),X67)|X67=k1_xboole_0)&(~r2_hidden(X69,X70)|~r2_hidden(X70,X71)|~r2_hidden(X71,X72)|~r2_hidden(X72,X73)|~r2_hidden(X73,esk2_1(X67))|r1_xboole_0(X69,X67)|X67=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.12/0.39  fof(c_0_61, plain, ![X54, X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|v1_relat_1(X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.39  fof(c_0_62, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.39  fof(c_0_63, plain, ![X52, X53]:(~v1_relat_1(X53)|~v1_funct_1(X53)|(~r2_hidden(X52,k1_relat_1(X53))|r2_hidden(k1_funct_1(X53,X52),k2_relat_1(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.12/0.39  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,esk5_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.12/0.39  cnf(c_0_65, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.39  cnf(c_0_66, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.12/0.39  cnf(c_0_67, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.12/0.39  cnf(c_0_68, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.12/0.39  cnf(c_0_69, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(esk2_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.12/0.39  cnf(c_0_70, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_66, c_0_43])).
% 0.12/0.39  fof(c_0_71, plain, ![X42, X43, X44, X45, X46]:~v1_xboole_0(k3_enumset1(X42,X43,X44,X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_subset_1])])).
% 0.12/0.39  cnf(c_0_72, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.12/0.39  cnf(c_0_73, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_65]), c_0_70])])).
% 0.12/0.39  cnf(c_0_74, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  fof(c_0_75, plain, ![X50, X51]:((~v5_relat_1(X51,X50)|r1_tarski(k2_relat_1(X51),X50)|~v1_relat_1(X51))&(~r1_tarski(k2_relat_1(X51),X50)|v5_relat_1(X51,X50)|~v1_relat_1(X51))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.12/0.39  fof(c_0_76, plain, ![X57, X58, X59]:((v4_relat_1(X59,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))&(v5_relat_1(X59,X58)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.39  cnf(c_0_77, plain, (~v1_xboole_0(k3_enumset1(X1,X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.12/0.39  cnf(c_0_78, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk5_0,esk3_0),X1)|~r1_tarski(k2_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_70])])).
% 0.12/0.39  cnf(c_0_79, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.12/0.39  cnf(c_0_80, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.12/0.39  cnf(c_0_81, plain, (~v1_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_37]), c_0_38]), c_0_39])).
% 0.12/0.39  cnf(c_0_82, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k1_funct_1(esk5_0,esk3_0),X1)|~v5_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_70])])).
% 0.12/0.39  cnf(c_0_83, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_80, c_0_43])).
% 0.12/0.39  cnf(c_0_84, negated_conjecture, (~r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  cnf(c_0_85, negated_conjecture, (~v1_xboole_0(k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_53])).
% 0.12/0.39  cnf(c_0_86, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.12/0.39  cnf(c_0_87, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.39  cnf(c_0_88, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.12/0.39  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_88])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 90
% 0.12/0.39  # Proof object clause steps            : 47
% 0.12/0.39  # Proof object formula steps           : 43
% 0.12/0.39  # Proof object conjectures             : 26
% 0.12/0.39  # Proof object clause conjectures      : 23
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 26
% 0.12/0.39  # Proof object initial formulas used   : 22
% 0.12/0.39  # Proof object generating inferences   : 15
% 0.12/0.39  # Proof object simplifying inferences  : 40
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 22
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 39
% 0.12/0.39  # Removed in clause preprocessing      : 7
% 0.12/0.39  # Initial clauses in saturation        : 32
% 0.12/0.39  # Processed clauses                    : 167
% 0.12/0.39  # ...of these trivial                  : 3
% 0.12/0.39  # ...subsumed                          : 20
% 0.12/0.39  # ...remaining for further processing  : 144
% 0.12/0.39  # Other redundant clauses eliminated   : 9
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 0
% 0.12/0.39  # Backward-rewritten                   : 62
% 0.12/0.39  # Generated clauses                    : 208
% 0.12/0.39  # ...of the previous two non-trivial   : 223
% 0.12/0.39  # Contextual simplify-reflections      : 1
% 0.12/0.39  # Paramodulations                      : 184
% 0.12/0.39  # Factorizations                       : 16
% 0.12/0.39  # Equation resolutions                 : 9
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 46
% 0.12/0.39  #    Positive orientable unit clauses  : 5
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 2
% 0.12/0.39  #    Non-unit-clauses                  : 39
% 0.12/0.39  # Current number of unprocessed clauses: 86
% 0.12/0.39  # ...number of literals in the above   : 395
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 101
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 1225
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 519
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 21
% 0.12/0.39  # Unit Clause-clause subsumption calls : 7
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 5
% 0.12/0.39  # BW rewrite match successes           : 2
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 6495
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.037 s
% 0.12/0.39  # System time              : 0.005 s
% 0.12/0.39  # Total time               : 0.042 s
% 0.12/0.39  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
