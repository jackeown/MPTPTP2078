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
% DateTime   : Thu Dec  3 11:06:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 111 expanded)
%              Number of clauses        :   33 (  46 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 445 expanded)
%              Number of equality atoms :   19 (  46 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(c_0_12,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | m1_subset_1(k1_relset_1(X32,X33,X34),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_13,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k1_relset_1(X35,X36,X37) = k1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_16,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,negated_conjecture,(
    ! [X47] :
      ( v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk3_0,esk4_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0))
      & ( ~ m1_subset_1(X47,esk3_0)
        | ~ r2_hidden(X47,esk5_0)
        | esk7_0 != k1_funct_1(esk6_0,X47) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(X29,k1_relat_1(X31))
        | ~ r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( X30 = k1_funct_1(X31,X29)
        | ~ r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( ~ r2_hidden(X29,k1_relat_1(X31))
        | X30 != k1_funct_1(X31,X29)
        | r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_23,plain,(
    ! [X24,X25,X26,X28] :
      ( ( r2_hidden(esk2_3(X24,X25,X26),k1_relat_1(X26))
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk2_3(X24,X25,X26),X24),X26)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(esk2_3(X24,X25,X26),X25)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(X28,k1_relat_1(X26))
        | ~ r2_hidden(k4_tarski(X28,X24),X26)
        | ~ r2_hidden(X28,X25)
        | r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | v1_relat_1(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_25,plain,(
    ! [X22,X23] : v1_relat_1(k2_zfmisc_1(X22,X23)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X4,k1_relset_1(X2,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_31,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X14,X13)
        | r2_hidden(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ r2_hidden(X14,X13)
        | m1_subset_1(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ m1_subset_1(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_xboole_0(X13) )
      & ( ~ v1_xboole_0(X14)
        | m1_subset_1(X14,X13)
        | ~ v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X4,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0)
    | esk7_0 != k1_funct_1(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( k1_funct_1(X1,esk2_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_34])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( esk7_0 != X1
    | ~ m1_subset_1(esk2_3(X1,X2,esk6_0),esk3_0)
    | ~ r2_hidden(esk2_3(X1,X2,esk6_0),esk5_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( esk7_0 != X1
    | ~ r2_hidden(esk2_3(X1,X2,esk6_0),k1_relat_1(esk6_0))
    | ~ r2_hidden(esk2_3(X1,X2,esk6_0),esk5_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_49,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_50,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k7_relset_1(X38,X39,X40,X41) = k9_relat_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_51,negated_conjecture,
    ( esk7_0 != X1
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk6_0),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_42])])).

cnf(c_0_52,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( esk7_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_42])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk7_0,k9_relat_1(esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_55,c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.53  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.53  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.53  #
% 0.19/0.53  # Preprocessing time       : 0.028 s
% 0.19/0.53  # Presaturation interreduction done
% 0.19/0.53  
% 0.19/0.53  # Proof found!
% 0.19/0.53  # SZS status Theorem
% 0.19/0.53  # SZS output start CNFRefutation
% 0.19/0.53  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.19/0.53  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.53  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 0.19/0.53  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.53  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.53  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.53  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.53  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.53  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.53  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.53  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.53  fof(c_0_12, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|m1_subset_1(k1_relset_1(X32,X33,X34),k1_zfmisc_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.19/0.53  fof(c_0_13, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k1_relset_1(X35,X36,X37)=k1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.53  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 0.19/0.53  fof(c_0_15, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.53  fof(c_0_16, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.53  fof(c_0_17, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.53  cnf(c_0_18, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.53  cnf(c_0_19, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.53  fof(c_0_20, negated_conjecture, ![X47]:(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0))&(~m1_subset_1(X47,esk3_0)|(~r2_hidden(X47,esk5_0)|esk7_0!=k1_funct_1(esk6_0,X47))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.19/0.53  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.53  fof(c_0_22, plain, ![X29, X30, X31]:(((r2_hidden(X29,k1_relat_1(X31))|~r2_hidden(k4_tarski(X29,X30),X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(X30=k1_funct_1(X31,X29)|~r2_hidden(k4_tarski(X29,X30),X31)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&(~r2_hidden(X29,k1_relat_1(X31))|X30!=k1_funct_1(X31,X29)|r2_hidden(k4_tarski(X29,X30),X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.53  fof(c_0_23, plain, ![X24, X25, X26, X28]:((((r2_hidden(esk2_3(X24,X25,X26),k1_relat_1(X26))|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))&(r2_hidden(k4_tarski(esk2_3(X24,X25,X26),X24),X26)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(r2_hidden(esk2_3(X24,X25,X26),X25)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(~r2_hidden(X28,k1_relat_1(X26))|~r2_hidden(k4_tarski(X28,X24),X26)|~r2_hidden(X28,X25)|r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.53  fof(c_0_24, plain, ![X20, X21]:(~v1_relat_1(X20)|(~m1_subset_1(X21,k1_zfmisc_1(X20))|v1_relat_1(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.53  fof(c_0_25, plain, ![X22, X23]:v1_relat_1(k2_zfmisc_1(X22,X23)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.53  cnf(c_0_26, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.53  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_28, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.53  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.53  cnf(c_0_30, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X2)|~r2_hidden(X4,k1_relset_1(X2,X3,X1))), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.19/0.53  cnf(c_0_31, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.53  cnf(c_0_32, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.53  cnf(c_0_33, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.53  cnf(c_0_34, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.53  fof(c_0_35, plain, ![X13, X14]:(((~m1_subset_1(X14,X13)|r2_hidden(X14,X13)|v1_xboole_0(X13))&(~r2_hidden(X14,X13)|m1_subset_1(X14,X13)|v1_xboole_0(X13)))&((~m1_subset_1(X14,X13)|v1_xboole_0(X14)|~v1_xboole_0(X13))&(~v1_xboole_0(X14)|m1_subset_1(X14,X13)|~v1_xboole_0(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.53  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.53  cnf(c_0_37, negated_conjecture, (m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.53  cnf(c_0_38, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X2)|~r2_hidden(X4,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_19])).
% 0.19/0.53  cnf(c_0_39, negated_conjecture, (~m1_subset_1(X1,esk3_0)|~r2_hidden(X1,esk5_0)|esk7_0!=k1_funct_1(esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.53  cnf(c_0_40, plain, (k1_funct_1(X1,esk2_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.53  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.53  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_34])])).
% 0.19/0.53  cnf(c_0_43, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.53  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.53  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk3_0)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_29])).
% 0.19/0.53  cnf(c_0_46, negated_conjecture, (esk7_0!=X1|~m1_subset_1(esk2_3(X1,X2,esk6_0),esk3_0)|~r2_hidden(esk2_3(X1,X2,esk6_0),esk5_0)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])])).
% 0.19/0.53  cnf(c_0_47, negated_conjecture, (m1_subset_1(X1,esk3_0)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.53  cnf(c_0_48, negated_conjecture, (esk7_0!=X1|~r2_hidden(esk2_3(X1,X2,esk6_0),k1_relat_1(esk6_0))|~r2_hidden(esk2_3(X1,X2,esk6_0),esk5_0)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.53  cnf(c_0_49, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.53  fof(c_0_50, plain, ![X38, X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k7_relset_1(X38,X39,X40,X41)=k9_relat_1(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.53  cnf(c_0_51, negated_conjecture, (esk7_0!=X1|~r2_hidden(esk2_3(X1,esk5_0,esk6_0),k1_relat_1(esk6_0))|~r2_hidden(X1,k9_relat_1(esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_42])])).
% 0.19/0.53  cnf(c_0_52, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.53  cnf(c_0_53, negated_conjecture, (r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.53  cnf(c_0_54, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.53  cnf(c_0_55, negated_conjecture, (esk7_0!=X1|~r2_hidden(X1,k9_relat_1(esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_42])])).
% 0.19/0.53  cnf(c_0_56, negated_conjecture, (r2_hidden(esk7_0,k9_relat_1(esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29])])).
% 0.19/0.53  cnf(c_0_57, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_55, c_0_56]), ['proof']).
% 0.19/0.53  # SZS output end CNFRefutation
% 0.19/0.53  # Proof object total steps             : 58
% 0.19/0.53  # Proof object clause steps            : 33
% 0.19/0.53  # Proof object formula steps           : 25
% 0.19/0.53  # Proof object conjectures             : 18
% 0.19/0.53  # Proof object clause conjectures      : 15
% 0.19/0.53  # Proof object formula conjectures     : 3
% 0.19/0.53  # Proof object initial clauses used    : 17
% 0.19/0.53  # Proof object initial formulas used   : 12
% 0.19/0.53  # Proof object generating inferences   : 16
% 0.19/0.53  # Proof object simplifying inferences  : 12
% 0.19/0.53  # Training examples: 0 positive, 0 negative
% 0.19/0.53  # Parsed axioms                        : 12
% 0.19/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.53  # Initial clauses                      : 27
% 0.19/0.53  # Removed in clause preprocessing      : 0
% 0.19/0.53  # Initial clauses in saturation        : 27
% 0.19/0.53  # Processed clauses                    : 1914
% 0.19/0.53  # ...of these trivial                  : 375
% 0.19/0.53  # ...subsumed                          : 644
% 0.19/0.53  # ...remaining for further processing  : 895
% 0.19/0.53  # Other redundant clauses eliminated   : 1
% 0.19/0.53  # Clauses deleted for lack of memory   : 0
% 0.19/0.53  # Backward-subsumed                    : 53
% 0.19/0.53  # Backward-rewritten                   : 16
% 0.19/0.53  # Generated clauses                    : 7869
% 0.19/0.53  # ...of the previous two non-trivial   : 6511
% 0.19/0.53  # Contextual simplify-reflections      : 41
% 0.19/0.53  # Paramodulations                      : 7858
% 0.19/0.53  # Factorizations                       : 6
% 0.19/0.53  # Equation resolutions                 : 2
% 0.19/0.53  # Propositional unsat checks           : 0
% 0.19/0.53  #    Propositional check models        : 0
% 0.19/0.53  #    Propositional check unsatisfiable : 0
% 0.19/0.53  #    Propositional clauses             : 0
% 0.19/0.53  #    Propositional clauses after purity: 0
% 0.19/0.53  #    Propositional unsat core size     : 0
% 0.19/0.53  #    Propositional preprocessing time  : 0.000
% 0.19/0.53  #    Propositional encoding time       : 0.000
% 0.19/0.53  #    Propositional solver time         : 0.000
% 0.19/0.53  #    Success case prop preproc time    : 0.000
% 0.19/0.53  #    Success case prop encoding time   : 0.000
% 0.19/0.53  #    Success case prop solver time     : 0.000
% 0.19/0.53  # Current number of processed clauses  : 796
% 0.19/0.53  #    Positive orientable unit clauses  : 122
% 0.19/0.53  #    Positive unorientable unit clauses: 0
% 0.19/0.53  #    Negative unit clauses             : 115
% 0.19/0.53  #    Non-unit-clauses                  : 559
% 0.19/0.53  # Current number of unprocessed clauses: 4373
% 0.19/0.53  # ...number of literals in the above   : 15880
% 0.19/0.53  # Current number of archived formulas  : 0
% 0.19/0.53  # Current number of archived clauses   : 99
% 0.19/0.53  # Clause-clause subsumption calls (NU) : 26838
% 0.19/0.53  # Rec. Clause-clause subsumption calls : 12435
% 0.19/0.53  # Non-unit clause-clause subsumptions  : 618
% 0.19/0.53  # Unit Clause-clause subsumption calls : 222
% 0.19/0.53  # Rewrite failures with RHS unbound    : 0
% 0.19/0.53  # BW rewrite match attempts            : 3622
% 0.19/0.53  # BW rewrite match successes           : 11
% 0.19/0.53  # Condensation attempts                : 0
% 0.19/0.53  # Condensation successes               : 0
% 0.19/0.53  # Termbank termtop insertions          : 141896
% 0.19/0.54  
% 0.19/0.54  # -------------------------------------------------
% 0.19/0.54  # User time                : 0.185 s
% 0.19/0.54  # System time              : 0.011 s
% 0.19/0.54  # Total time               : 0.195 s
% 0.19/0.54  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
