%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t63_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:11 EDT 2019

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  111 (2108 expanded)
%              Number of clauses        :   74 ( 919 expanded)
%              Number of leaves         :   19 ( 552 expanded)
%              Depth                    :   21
%              Number of atoms          :  323 (6303 expanded)
%              Number of equality atoms :  150 (2949 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t3_subset)).

fof(t63_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ~ ( ~ r1_tarski(X1,k4_zfmisc_1(X1,X2,X3,X4))
          & ~ r1_tarski(X1,k4_zfmisc_1(X2,X3,X4,X1))
          & ~ r1_tarski(X1,k4_zfmisc_1(X3,X4,X1,X2))
          & ~ r1_tarski(X1,k4_zfmisc_1(X4,X1,X2,X3)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t63_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',d3_mcart_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t34_mcart_1)).

fof(t54_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t54_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t60_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',dt_k9_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t2_subset)).

fof(t49_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
          & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
          & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t49_mcart_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',dt_k8_mcart_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t55_mcart_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t5_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',d2_xboole_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',existence_m1_subset_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t63_mcart_1.p',t3_xboole_1)).

fof(c_0_19,plain,(
    ! [X58,X59,X60] :
      ( ~ r2_hidden(X58,X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(X60))
      | m1_subset_1(X58,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_20,plain,(
    ! [X52,X53] :
      ( ( ~ m1_subset_1(X52,k1_zfmisc_1(X53))
        | r1_tarski(X52,X53) )
      & ( ~ r1_tarski(X52,X53)
        | m1_subset_1(X52,k1_zfmisc_1(X53)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ~ ( ~ r1_tarski(X1,k4_zfmisc_1(X1,X2,X3,X4))
            & ~ r1_tarski(X1,k4_zfmisc_1(X2,X3,X4,X1))
            & ~ r1_tarski(X1,k4_zfmisc_1(X3,X4,X1,X2))
            & ~ r1_tarski(X1,k4_zfmisc_1(X4,X1,X2,X3)) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t63_mcart_1])).

fof(c_0_22,plain,(
    ! [X16,X17,X18,X19] : k4_mcart_1(X16,X17,X18,X19) = k4_tarski(k3_mcart_1(X16,X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_23,plain,(
    ! [X13,X14,X15] : k3_mcart_1(X13,X14,X15) = k4_tarski(k4_tarski(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X46,X48,X49,X50,X51] :
      ( ( r2_hidden(esk6_1(X46),X46)
        | X46 = k1_xboole_0 )
      & ( ~ r2_hidden(X48,X46)
        | esk6_1(X46) != k4_mcart_1(X48,X49,X50,X51)
        | X46 = k1_xboole_0 )
      & ( ~ r2_hidden(X49,X46)
        | esk6_1(X46) != k4_mcart_1(X48,X49,X50,X51)
        | X46 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_27,negated_conjecture,
    ( ( r1_tarski(esk1_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | r1_tarski(esk1_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk1_0))
      | r1_tarski(esk1_0,k4_zfmisc_1(esk3_0,esk4_0,esk1_0,esk2_0))
      | r1_tarski(esk1_0,k4_zfmisc_1(esk4_0,esk1_0,esk2_0,esk3_0)) )
    & esk1_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_28,plain,(
    ! [X61,X62,X63,X64] : k3_zfmisc_1(k2_zfmisc_1(X61,X62),X63,X64) = k4_zfmisc_1(X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t54_mcart_1])).

fof(c_0_29,plain,(
    ! [X72,X73,X74,X75,X76] :
      ( X72 = k1_xboole_0
      | X73 = k1_xboole_0
      | X74 = k1_xboole_0
      | X75 = k1_xboole_0
      | ~ m1_subset_1(X76,k4_zfmisc_1(X72,X73,X74,X75))
      | X76 = k4_mcart_1(k8_mcart_1(X72,X73,X74,X75,X76),k9_mcart_1(X72,X73,X74,X75,X76),k10_mcart_1(X72,X73,X74,X75,X76),k11_mcart_1(X72,X73,X74,X75,X76)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

cnf(c_0_30,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk1_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | r1_tarski(esk1_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk1_0))
    | r1_tarski(esk1_0,k4_zfmisc_1(esk3_0,esk4_0,esk1_0,esk2_0))
    | r1_tarski(esk1_0,k4_zfmisc_1(esk4_0,esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ~ m1_subset_1(X39,k4_zfmisc_1(X35,X36,X37,X38))
      | m1_subset_1(k9_mcart_1(X35,X36,X37,X38,X39),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk6_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk1_0,esk2_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk1_0),esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_42,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X44,X45)
      | v1_xboole_0(X45)
      | r2_hidden(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k4_mcart_1(X3,X1,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_1(esk1_0),k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk1_0),esk2_0,esk3_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk1_0,esk2_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(X2,X3),X4,X5)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_49,plain,
    ( X2 = k1_xboole_0
    | esk6_1(X2) != k4_tarski(k4_tarski(k4_tarski(X3,X1),X4),X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk4_0,esk1_0,esk2_0,esk3_0,esk6_1(esk1_0)),k9_mcart_1(esk4_0,esk1_0,esk2_0,esk3_0,esk6_1(esk1_0))),k10_mcart_1(esk4_0,esk1_0,esk2_0,esk3_0,esk6_1(esk1_0))),k11_mcart_1(esk4_0,esk1_0,esk2_0,esk3_0,esk6_1(esk1_0))) = esk6_1(esk1_0)
    | esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_41])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(k9_mcart_1(X2,X1,X3,X4,X5),X1)
    | ~ m1_subset_1(X5,k3_zfmisc_1(k2_zfmisc_1(X2,X1),X3,X4)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_52,plain,(
    ! [X55,X56,X57] :
      ( ( ~ r1_tarski(X55,k3_zfmisc_1(X55,X56,X57))
        | X55 = k1_xboole_0 )
      & ( ~ r1_tarski(X55,k3_zfmisc_1(X56,X57,X55))
        | X55 = k1_xboole_0 )
      & ( ~ r1_tarski(X55,k3_zfmisc_1(X57,X55,X56))
        | X55 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk1_0,esk2_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0))
    | esk6_1(X1) != esk6_1(esk1_0)
    | ~ r2_hidden(k9_mcart_1(esk4_0,esk1_0,esk2_0,esk3_0,esk6_1(esk1_0)),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(esk1_0)
    | r2_hidden(k9_mcart_1(esk4_0,esk1_0,esk2_0,esk3_0,esk6_1(esk1_0)),esk1_0)
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_46])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X2,X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v1_xboole_0(esk1_0)
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_41])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | v1_xboole_0(esk1_0)
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_41])).

fof(c_0_59,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ~ m1_subset_1(X34,k4_zfmisc_1(X30,X31,X32,X33))
      | m1_subset_1(k8_mcart_1(X30,X31,X32,X33,X34),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v1_xboole_0(esk1_0)
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_41])).

cnf(c_0_61,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_62,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k4_mcart_1(X1,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | v1_xboole_0(esk1_0)
    | m1_subset_1(esk6_1(esk1_0),k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_60]),c_0_41])).

cnf(c_0_64,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(X2,X3),X4,X5)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_35])).

cnf(c_0_65,plain,
    ( X2 = k1_xboole_0
    | esk6_1(X2) != k4_tarski(k4_tarski(k4_tarski(X1,X3),X4),X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_38])).

cnf(c_0_66,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_1(esk1_0)),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_1(esk1_0))),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_1(esk1_0))),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_1(esk1_0))) = esk6_1(esk1_0)
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | v1_xboole_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_63]),c_0_41])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(k8_mcart_1(X1,X2,X3,X4,X5),X1)
    | ~ m1_subset_1(X5,k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_64])).

fof(c_0_68,plain,(
    ! [X65,X66,X67,X68] :
      ( ( X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | X68 = k1_xboole_0
        | k4_zfmisc_1(X65,X66,X67,X68) != k1_xboole_0 )
      & ( X65 != k1_xboole_0
        | k4_zfmisc_1(X65,X66,X67,X68) = k1_xboole_0 )
      & ( X66 != k1_xboole_0
        | k4_zfmisc_1(X65,X66,X67,X68) = k1_xboole_0 )
      & ( X67 != k1_xboole_0
        | k4_zfmisc_1(X65,X66,X67,X68) = k1_xboole_0 )
      & ( X68 != k1_xboole_0
        | k4_zfmisc_1(X65,X66,X67,X68) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

fof(c_0_69,plain,(
    ! [X69,X70,X71] :
      ( ~ r2_hidden(X69,X70)
      | ~ m1_subset_1(X70,k1_zfmisc_1(X71))
      | ~ v1_xboole_0(X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_70,plain,(
    ! [X77] :
      ( ~ v1_xboole_0(X77)
      | X77 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | v1_xboole_0(esk1_0)
    | esk6_1(X1) != esk6_1(esk1_0)
    | ~ r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_1(esk1_0)),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v1_xboole_0(esk1_0)
    | r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_1(esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_73,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | v1_xboole_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_41])).

cnf(c_0_80,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X2,X3),X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_35])).

cnf(c_0_81,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X2,X3),X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_35])).

cnf(c_0_82,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X2,X1),X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_35])).

cnf(c_0_83,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_76,c_0_35])).

cnf(c_0_84,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_25])).

cnf(c_0_85,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_41])).

cnf(c_0_86,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_88,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_89,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_91,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

fof(c_0_92,plain,(
    ! [X40] : m1_subset_1(esk5_1(X40),X40) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_93,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_33])).

cnf(c_0_94,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_85]),c_0_86]),c_0_87]),c_0_88]),c_0_89])])).

cnf(c_0_95,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

fof(c_0_96,plain,(
    ! [X54] :
      ( ~ r1_tarski(X54,k1_xboole_0)
      | X54 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_98,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])]),c_0_41])).

cnf(c_0_100,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_101,plain,
    ( r1_tarski(esk5_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk1_0,esk2_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0))
    | ~ v1_xboole_0(k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk1_0),esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_40]),c_0_41])).

cnf(c_0_103,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_99]),c_0_87]),c_0_88]),c_0_89]),c_0_86])])).

cnf(c_0_104,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk5_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_98])).

cnf(c_0_105,plain,
    ( esk5_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk6_1(esk1_0),k3_zfmisc_1(k2_zfmisc_1(esk4_0,esk1_0),esk2_0,esk3_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk1_0))
    | r1_tarski(esk1_0,k3_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_46]),c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_103]),c_0_95])]),c_0_41])).

cnf(c_0_108,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_95])])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(esk1_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107]),c_0_87]),c_0_107]),c_0_88]),c_0_107]),c_0_89]),c_0_107]),c_0_86])]),c_0_108])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_109]),c_0_95])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
