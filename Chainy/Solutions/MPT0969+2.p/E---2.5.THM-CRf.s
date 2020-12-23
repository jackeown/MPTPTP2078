%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0969+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:59 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 194 expanded)
%              Number of clauses        :   37 (  79 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 627 expanded)
%              Number of equality atoms :   39 ( 116 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => r2_hidden(X2,k1_funct_2(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',d19_relat_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t5_subset)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(t2_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3] :
                  ( r2_hidden(X3,X2)
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT012+2.ax',t2_mcart_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT012+2.ax',t34_mcart_1)).

fof(t11_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',fc1_xboole_0)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT009+2.ax',t45_ordinal1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',t4_subset_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => r2_hidden(X2,k1_funct_2(X1,X1)) ) ),
    inference(assume_negation,[status(cth)],[t12_funct_2])).

fof(c_0_16,plain,(
    ! [X3487,X3488,X3489] :
      ( ( v4_relat_1(X3489,X3487)
        | ~ m1_subset_1(X3489,k1_zfmisc_1(k2_zfmisc_1(X3487,X3488))) )
      & ( v5_relat_1(X3489,X3488)
        | ~ m1_subset_1(X3489,k1_zfmisc_1(k2_zfmisc_1(X3487,X3488))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_17,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & ~ r2_hidden(esk2_0,k1_funct_2(esk1_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X669,X670] :
      ( ~ v1_relat_1(X669)
      | ~ m1_subset_1(X670,k1_zfmisc_1(X669))
      | v1_relat_1(X670) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_19,plain,(
    ! [X825,X826] : v1_relat_1(k2_zfmisc_1(X825,X826)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_20,plain,(
    ! [X2445,X2446] :
      ( ( ~ v5_relat_1(X2446,X2445)
        | r1_tarski(k2_relat_1(X2446),X2445)
        | ~ v1_relat_1(X2446) )
      & ( ~ r1_tarski(k2_relat_1(X2446),X2445)
        | v5_relat_1(X2446,X2445)
        | ~ v1_relat_1(X2446) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_21,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X922,X923] :
      ( ( v1_funct_1(X923)
        | ~ r1_tarski(k2_relat_1(X923),X922)
        | ~ v1_relat_1(X923)
        | ~ v1_funct_1(X923) )
      & ( v1_funct_2(X923,k1_relat_1(X923),X922)
        | ~ r1_tarski(k2_relat_1(X923),X922)
        | ~ v1_relat_1(X923)
        | ~ v1_funct_1(X923) )
      & ( m1_subset_1(X923,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X923),X922)))
        | ~ r1_tarski(k2_relat_1(X923),X922)
        | ~ v1_relat_1(X923)
        | ~ v1_funct_1(X923) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_24])])).

fof(c_0_29,plain,(
    ! [X352,X353,X354] :
      ( ~ r2_hidden(X352,X353)
      | ~ m1_subset_1(X353,k1_zfmisc_1(X354))
      | ~ v1_xboole_0(X354) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_30,plain,(
    ! [X918,X919] :
      ( m1_subset_1(esk122_2(X918,X919),k1_zfmisc_1(k2_zfmisc_1(X918,X919)))
      & v1_relat_1(esk122_2(X918,X919))
      & v4_relat_1(esk122_2(X918,X919),X918)
      & v5_relat_1(esk122_2(X918,X919),X919)
      & v1_funct_1(esk122_2(X918,X919))
      & v1_funct_2(esk122_2(X918,X919),X918,X919) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_34,plain,(
    ! [X739,X740] :
      ( ( k2_zfmisc_1(X739,X740) != k1_xboole_0
        | X739 = k1_xboole_0
        | X740 = k1_xboole_0 )
      & ( X739 != k1_xboole_0
        | k2_zfmisc_1(X739,X740) = k1_xboole_0 )
      & ( X740 != k1_xboole_0
        | k2_zfmisc_1(X739,X740) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk122_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X562,X564] :
      ( ( r2_hidden(esk90_1(X562),X562)
        | X562 = k1_xboole_0 )
      & ( ~ r2_hidden(X564,esk90_1(X562))
        | r1_xboole_0(X564,X562)
        | X562 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_mcart_1])])])])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_28])])).

fof(c_0_39,plain,(
    ! [X4104,X4106,X4107,X4108,X4109] :
      ( ( r2_hidden(esk400_1(X4104),X4104)
        | X4104 = k1_xboole_0 )
      & ( ~ r2_hidden(X4106,X4104)
        | esk400_1(X4104) != k4_mcart_1(X4106,X4107,X4108,X4109)
        | X4104 = k1_xboole_0 )
      & ( ~ r2_hidden(X4107,X4104)
        | esk400_1(X4104) != k4_mcart_1(X4106,X4107,X4108,X4109)
        | X4104 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_40,plain,(
    ! [X644,X645,X646] :
      ( ( X645 = k1_xboole_0
        | r2_hidden(X646,k1_funct_2(X644,X645))
        | ~ v1_funct_1(X646)
        | ~ v1_funct_2(X646,X644,X645)
        | ~ m1_subset_1(X646,k1_zfmisc_1(k2_zfmisc_1(X644,X645))) )
      & ( X644 != k1_xboole_0
        | r2_hidden(X646,k1_funct_2(X644,X645))
        | ~ v1_funct_1(X646)
        | ~ v1_funct_2(X646,X644,X645)
        | ~ m1_subset_1(X646,k1_zfmisc_1(k2_zfmisc_1(X644,X645))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,esk122_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(esk90_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(esk400_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_funct_2(esk1_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( r2_hidden(X2,k1_funct_2(X1,X3))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( esk122_2(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_54,plain,(
    ! [X3477] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X3477)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

fof(c_0_55,plain,(
    ! [X653] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X653)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_33]),c_0_22])]),c_0_48])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_51])).

cnf(c_0_60,plain,
    ( v1_funct_2(esk122_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_61,plain,
    ( esk122_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_53])])).

cnf(c_0_62,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_53])])).

cnf(c_0_65,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_61]),c_0_62]),c_0_61]),c_0_63])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_57]),c_0_57]),c_0_64]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
