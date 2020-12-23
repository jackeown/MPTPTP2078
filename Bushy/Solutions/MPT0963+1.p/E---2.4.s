%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t5_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:47 EDT 2019

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  187 (13770 expanded)
%              Number of clauses        :  155 (6754 expanded)
%              Number of leaves         :   16 (3523 expanded)
%              Depth                    :   33
%              Number of atoms          :  552 (44864 expanded)
%              Number of equality atoms :  100 (4342 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_funct_2,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',t5_funct_2)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',t7_boole)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',redefinition_k1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',d3_tarski)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',cc4_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',t8_boole)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',dt_k1_relset_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',dt_o_0_0_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',d5_funct_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',t2_subset)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',t11_relset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',t6_boole)).

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
    file('/export/starexec/sandbox/benchmark/funct_2__t5_funct_2.p',d1_funct_2)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( k1_relat_1(X3) = X1
            & ! [X4] :
                ( r2_hidden(X4,X1)
               => r2_hidden(k1_funct_1(X3,X4),X2) ) )
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_funct_2])).

fof(c_0_17,plain,(
    ! [X54,X55] :
      ( ~ r2_hidden(X54,X55)
      | ~ v1_xboole_0(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_18,negated_conjecture,(
    ! [X8] :
      ( v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & k1_relat_1(esk3_0) = esk1_0
      & ( ~ r2_hidden(X8,esk1_0)
        | r2_hidden(k1_funct_1(esk3_0,X8),esk2_0) )
      & ( ~ v1_funct_1(esk3_0)
        | ~ v1_funct_2(esk3_0,esk1_0,esk2_0)
        | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k1_relset_1(X35,X36,X37) = k1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_20,plain,(
    ! [X45,X46] :
      ( ( ~ m1_subset_1(X45,k1_zfmisc_1(X46))
        | r1_tarski(X45,X46) )
      & ( ~ r1_tarski(X45,X46)
        | m1_subset_1(X45,k1_zfmisc_1(X46)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,X1),esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r1_tarski(X14,X15)
        | ~ r2_hidden(X16,X14)
        | r2_hidden(X16,X15) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r1_tarski(X17,X18) )
      & ( ~ r2_hidden(esk4_2(X17,X18),X18)
        | r1_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_24,plain,(
    ! [X58,X59,X60] :
      ( ~ v1_xboole_0(X58)
      | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))
      | v1_xboole_0(X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_25,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X56,X57] :
      ( ~ v1_xboole_0(X56)
      | X56 = X57
      | ~ v1_xboole_0(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | m1_subset_1(k1_relset_1(X30,X31,X32),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_33,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k1_relset_1(X1,X2,esk1_0) = k1_relat_1(esk1_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk1_0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk2_0)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_45,plain,(
    ! [X20,X21,X22,X24,X25,X26,X28] :
      ( ( r2_hidden(esk5_3(X20,X21,X22),k1_relat_1(X20))
        | ~ r2_hidden(X22,X21)
        | X21 != k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X22 = k1_funct_1(X20,esk5_3(X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(X25,k1_relat_1(X20))
        | X24 != k1_funct_1(X20,X25)
        | r2_hidden(X24,X21)
        | X21 != k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(esk6_2(X20,X26),X26)
        | ~ r2_hidden(X28,k1_relat_1(X20))
        | esk6_2(X20,X26) != k1_funct_1(X20,X28)
        | X26 = k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(esk7_2(X20,X26),k1_relat_1(X20))
        | r2_hidden(esk6_2(X20,X26),X26)
        | X26 = k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( esk6_2(X20,X26) = k1_funct_1(X20,esk7_2(X20,X26))
        | r2_hidden(esk6_2(X20,X26),X26)
        | X26 = k2_relat_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk1_0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk1_0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk2_0)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_50,plain,
    ( r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_51,plain,(
    ! [X50,X51,X52] :
      ( ~ r2_hidden(X50,X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(X52))
      | ~ v1_xboole_0(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_52,plain,(
    ! [X33] : m1_subset_1(esk8_1(X33),X33) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk1_0))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( ~ v1_xboole_0(k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_50])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_57,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X43,X44)
      | v1_xboole_0(X44)
      | r2_hidden(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk1_0))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_26]),c_0_34])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_xboole_0(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk8_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_42])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk1_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_36])).

cnf(c_0_67,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),X1)
    | ~ v1_xboole_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_69,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,esk8_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(X1,X2) = k1_relat_1(esk1_0)
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_56])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k1_relat_1(esk1_0))))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk3_0))
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_64])).

cnf(c_0_76,plain,
    ( X1 = esk8_1(k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k1_relat_1(esk1_0))))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk3_0))
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_56])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_64])).

cnf(c_0_80,plain,
    ( r1_tarski(esk8_1(k1_zfmisc_1(X1)),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_28])).

cnf(c_0_81,negated_conjecture,
    ( esk8_1(k1_zfmisc_1(X1)) = k1_relat_1(esk1_0)
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( X1 = esk8_1(k1_zfmisc_1(k1_relat_1(esk1_0)))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk3_0))
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_56])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),X1)
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( v1_xboole_0(k1_relset_1(o_0_0_xboole_0,X1,X2))
    | ~ v1_xboole_0(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_39])).

cnf(c_0_87,plain,
    ( k1_relset_1(X1,X2,esk8_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k1_relat_1(esk8_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_56])).

cnf(c_0_88,negated_conjecture,
    ( esk8_1(k1_zfmisc_1(k1_relat_1(esk1_0))) = k2_relat_1(esk3_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),X1)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_36])).

cnf(c_0_90,plain,
    ( v1_xboole_0(k1_relat_1(esk8_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))))
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_56]),c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk3_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k1_relset_1(X1,X2,k1_relat_1(esk1_0)) = k1_relat_1(k1_relat_1(esk1_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk1_0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_26]),c_0_34])).

fof(c_0_94,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ r1_tarski(k1_relat_1(X40),X38)
      | ~ r1_tarski(k2_relat_1(X40),X39)
      | m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_95,plain,
    ( v1_xboole_0(k1_relat_1(esk8_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_36])).

cnf(c_0_96,negated_conjecture,
    ( k2_zfmisc_1(X1,X2) = k2_relat_1(esk3_0)
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k1_relat_1(k1_relat_1(esk1_0)),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_92]),c_0_93])).

cnf(c_0_98,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_99,plain,
    ( k1_relat_1(esk8_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k2_relat_1(esk3_0))))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_97])).

cnf(c_0_102,plain,
    ( esk8_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = o_0_0_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_70])).

cnf(c_0_103,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(k1_relat_1(X3),X1)
    | ~ r1_tarski(k2_relat_1(X3),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( k1_relat_1(esk8_1(k1_zfmisc_1(k1_relat_1(esk1_0)))) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_71])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k2_relat_1(esk3_0))))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_77])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_77])).

cnf(c_0_107,plain,
    ( esk8_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_44])).

cnf(c_0_108,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(k1_relat_1(X2),X3)
    | ~ r1_tarski(k2_relat_1(X2),X1)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_44]),c_0_36])])).

cnf(c_0_109,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r2_hidden(X4,k1_relset_1(X1,X3,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_39])).

cnf(c_0_110,negated_conjecture,
    ( k1_relat_1(esk8_1(k1_zfmisc_1(k1_relat_1(esk1_0)))) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( esk8_1(k1_zfmisc_1(k1_relat_1(esk1_0))) = k1_relat_1(k1_relat_1(esk1_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_106])).

cnf(c_0_112,plain,
    ( esk8_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_107,c_0_36])).

cnf(c_0_113,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(k2_relat_1(X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_108,c_0_38])).

cnf(c_0_114,negated_conjecture,
    ( k2_zfmisc_1(X1,X2) = k2_relat_1(esk3_0)
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_83])).

fof(c_0_115,plain,(
    ! [X53] :
      ( ~ v1_xboole_0(X53)
      | X53 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_116,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relat_1(esk8_1(k1_zfmisc_1(k2_zfmisc_1(X1,X3))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_87]),c_0_56])])).

cnf(c_0_117,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_relat_1(esk1_0))) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_118,plain,
    ( ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_112]),c_0_36])])).

cnf(c_0_119,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_120,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_68]),c_0_62])])).

cnf(c_0_121,negated_conjecture,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k2_relat_1(esk3_0))))
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_114])).

cnf(c_0_122,negated_conjecture,
    ( ~ v1_funct_1(esk3_0)
    | ~ v1_funct_2(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_123,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v1_funct_2(X13,X11,X12)
        | X11 = k1_relset_1(X11,X12,X13)
        | X12 = k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X11 != k1_relset_1(X11,X12,X13)
        | v1_funct_2(X13,X11,X12)
        | X12 = k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( ~ v1_funct_2(X13,X11,X12)
        | X11 = k1_relset_1(X11,X12,X13)
        | X11 != k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X11 != k1_relset_1(X11,X12,X13)
        | v1_funct_2(X13,X11,X12)
        | X11 != k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( ~ v1_funct_2(X13,X11,X12)
        | X13 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 != k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X13 != k1_xboole_0
        | v1_funct_2(X13,X11,X12)
        | X11 = k1_xboole_0
        | X12 != k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_124,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_125,plain,
    ( X1 = k1_funct_1(X2,esk5_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_126,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k1_relat_1(o_0_0_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_44]),c_0_112])).

cnf(c_0_127,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(k1_relat_1(k1_relat_1(esk1_0))))
    | ~ v1_funct_1(k1_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k1_relat_1(k1_relat_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_117]),c_0_118])).

cnf(c_0_128,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_119])])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_120,c_0_28])).

cnf(c_0_130,negated_conjecture,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k2_relat_1(esk3_0))))
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_36])).

cnf(c_0_131,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_61])])).

cnf(c_0_132,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_133,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_124,c_0_36])).

cnf(c_0_134,plain,
    ( k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_125])).

cnf(c_0_135,plain,
    ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X1)
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_126,c_0_28])).

cnf(c_0_136,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,k1_relat_1(k1_relat_1(k1_relat_1(esk1_0))))
    | ~ v1_funct_1(k1_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k1_relat_1(k1_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_137,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_139,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk3_0),esk2_0)
    | ~ r1_tarski(esk1_0,esk1_0)
    | ~ v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_98]),c_0_60]),c_0_62])])).

cnf(c_0_140,plain,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(rw,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(esk5_3(esk3_0,k2_relat_1(esk3_0),X1),esk1_0)
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_134]),c_0_61]),c_0_62])])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(esk5_3(esk3_0,k2_relat_1(esk3_0),X1),esk1_0)
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_143,plain,
    ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_135,c_0_36])).

cnf(c_0_144,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_88]),c_0_66])).

cnf(c_0_145,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(k1_relat_1(k1_relat_1(esk1_0))))
    | ~ v1_xboole_0(esk2_0)
    | ~ m1_subset_1(X1,k1_relat_1(k1_relat_1(k1_relat_1(esk1_0))))
    | ~ v1_funct_1(k1_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k1_relat_1(k1_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_64])).

cnf(c_0_146,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_147,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk3_0),esk2_0)
    | ~ v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_38])])).

cnf(c_0_148,plain,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(k1_relat_1(X2),X3)
    | ~ r1_tarski(k2_relat_1(X2),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_140,c_0_98])).

cnf(c_0_149,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_150,plain,
    ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_143,c_0_36])).

cnf(c_0_151,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),X1)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_144,c_0_28])).

cnf(c_0_152,negated_conjecture,
    ( X1 = k1_relat_1(k1_relat_1(esk1_0))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_106])).

cnf(c_0_153,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(k1_relat_1(k1_relat_1(esk1_0))))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_funct_1(k1_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k1_relat_1(k1_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_145,c_0_56])).

cnf(c_0_154,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_130])).

cnf(c_0_155,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | k1_relset_1(esk1_0,esk2_0,esk3_0) != esk1_0
    | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_148]),c_0_60]),c_0_38]),c_0_62])])).

cnf(c_0_156,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(k1_relat_1(X3),X1)
    | ~ r1_tarski(k2_relat_1(X3),X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_98])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),X1)
    | r2_hidden(esk4_2(k2_relat_1(esk3_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_28])).

cnf(c_0_158,plain,
    ( esk8_1(k1_zfmisc_1(X1)) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_73])).

cnf(c_0_159,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_150])).

cnf(c_0_160,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_151]),c_0_62])])).

cnf(c_0_161,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_relat_1(esk1_0))) = k1_relat_1(k1_relat_1(esk1_0))
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_funct_1(k1_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k1_relat_1(k1_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_152,c_0_153])).

cnf(c_0_162,negated_conjecture,
    ( k1_relat_1(k1_relat_1(esk1_0)) = esk3_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_154]),c_0_84])).

cnf(c_0_163,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_156]),c_0_60]),c_0_60]),c_0_38]),c_0_62])])).

cnf(c_0_164,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_157])).

cnf(c_0_165,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_166,plain,
    ( r1_tarski(o_0_0_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_158])).

cnf(c_0_167,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_159,c_0_36])).

cnf(c_0_168,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_160,c_0_28])).

cnf(c_0_169,negated_conjecture,
    ( k1_relat_1(k1_relat_1(esk1_0)) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_106])).

cnf(c_0_170,negated_conjecture,
    ( esk3_0 = esk1_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_171,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_163,c_0_164])])).

cnf(c_0_172,plain,
    ( v1_funct_2(X1,o_0_0_xboole_0,X2)
    | k1_relset_1(o_0_0_xboole_0,X2,X1) != o_0_0_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_165]),c_0_133]),c_0_133]),c_0_133]),c_0_133])).

cnf(c_0_173,plain,
    ( r1_tarski(o_0_0_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_166,c_0_36])).

cnf(c_0_174,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_167])).

cnf(c_0_175,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_26])).

cnf(c_0_176,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_168,c_0_105])).

cnf(c_0_177,negated_conjecture,
    ( o_0_0_xboole_0 = esk3_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_169,c_0_162])).

cnf(c_0_178,negated_conjecture,
    ( esk3_0 = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_170,c_0_171]),c_0_36])])).

cnf(c_0_179,plain,
    ( v1_funct_2(X1,o_0_0_xboole_0,X2)
    | k1_relset_1(o_0_0_xboole_0,X2,X1) != o_0_0_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(o_0_0_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_172,c_0_26])).

cnf(c_0_180,plain,
    ( k1_relset_1(X1,X2,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_173]),c_0_174])).

cnf(c_0_181,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_175,c_0_176])).

cnf(c_0_182,negated_conjecture,
    ( o_0_0_xboole_0 = esk1_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_177,c_0_171]),c_0_36])]),c_0_178])).

cnf(c_0_183,plain,
    ( v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_173]),c_0_180])])).

cnf(c_0_184,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_181,c_0_171]),c_0_36]),c_0_171])]),c_0_178]),c_0_182])).

cnf(c_0_185,plain,
    ( v1_funct_2(esk1_0,esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_183,c_0_182]),c_0_182])).

cnf(c_0_186,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_184,c_0_185])]),
    [proof]).
%------------------------------------------------------------------------------
