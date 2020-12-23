%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t76_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:13 EDT 2019

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  115 (4440 expanded)
%              Number of clauses        :   86 (2201 expanded)
%              Number of leaves         :   15 (1163 expanded)
%              Depth                    :   18
%              Number of atoms          :  382 (13429 expanded)
%              Number of equality atoms :  211 (3813 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X1))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X2))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X3))
             => ! [X7] :
                  ( m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))
                 => ( r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))
                   => ( r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)
                      & r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5)
                      & r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t76_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t1_subset)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',dt_k5_mcart_1)).

fof(t75_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & X5 != k1_xboole_0
        & X6 != k1_xboole_0
        & ? [X7] :
            ( m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))
            & ? [X8] :
                ( m1_subset_1(X8,k3_zfmisc_1(X4,X5,X6))
                & X7 = X8
                & ~ ( k5_mcart_1(X1,X2,X3,X7) = k5_mcart_1(X4,X5,X6,X8)
                    & k6_mcart_1(X1,X2,X3,X7) = k6_mcart_1(X4,X5,X6,X8)
                    & k7_mcart_1(X1,X2,X3,X7) = k7_mcart_1(X4,X5,X6,X8) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t75_mcart_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',dt_k7_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',dt_k6_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',existence_m1_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t5_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',d2_xboole_0)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t35_mcart_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t8_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t76_mcart_1.p',t7_boole)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X1))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X2))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X3))
               => ! [X7] :
                    ( m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))
                   => ( r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))
                     => ( r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)
                        & r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5)
                        & r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_mcart_1])).

fof(c_0_16,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | m1_subset_1(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & r2_hidden(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( ~ r2_hidden(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk4_0)
      | ~ r2_hidden(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk5_0)
      | ~ r2_hidden(k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ m1_subset_1(X21,k3_zfmisc_1(X18,X19,X20))
      | m1_subset_1(k5_mcart_1(X18,X19,X20,X21),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54,X55] :
      ( ( k5_mcart_1(X48,X49,X50,X54) = k5_mcart_1(X51,X52,X53,X55)
        | ~ m1_subset_1(X55,k3_zfmisc_1(X51,X52,X53))
        | X54 != X55
        | ~ m1_subset_1(X54,k3_zfmisc_1(X48,X49,X50))
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0 )
      & ( k6_mcart_1(X48,X49,X50,X54) = k6_mcart_1(X51,X52,X53,X55)
        | ~ m1_subset_1(X55,k3_zfmisc_1(X51,X52,X53))
        | X54 != X55
        | ~ m1_subset_1(X54,k3_zfmisc_1(X48,X49,X50))
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0 )
      & ( k7_mcart_1(X48,X49,X50,X54) = k7_mcart_1(X51,X52,X53,X55)
        | ~ m1_subset_1(X55,k3_zfmisc_1(X51,X52,X53))
        | X54 != X55
        | ~ m1_subset_1(X54,k3_zfmisc_1(X48,X49,X50))
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_mcart_1])])])])).

fof(c_0_22,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X29,k3_zfmisc_1(X26,X27,X28))
      | m1_subset_1(k7_mcart_1(X26,X27,X28,X29),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

fof(c_0_23,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ m1_subset_1(X25,k3_zfmisc_1(X22,X23,X24))
      | m1_subset_1(k6_mcart_1(X22,X23,X24,X25),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

fof(c_0_24,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X34,X35)
      | v1_xboole_0(X35)
      | r2_hidden(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_25,plain,(
    ! [X30] : m1_subset_1(esk8_1(X30),X30) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k5_mcart_1(X5,X6,X7,X8)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | ~ m1_subset_1(X8,k3_zfmisc_1(X5,X6,X7))
    | X4 != X8
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k7_mcart_1(X5,X6,X7,X8)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | ~ m1_subset_1(X8,k3_zfmisc_1(X5,X6,X7))
    | X4 != X8
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k6_mcart_1(X5,X6,X7,X8)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | ~ m1_subset_1(X8,k3_zfmisc_1(X5,X6,X7))
    | X4 != X8
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X44,X45,X46] :
      ( ~ r2_hidden(X44,X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(X46))
      | ~ v1_xboole_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_34,plain,(
    ! [X47] :
      ( ~ v1_xboole_0(X47)
      | X47 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k5_mcart_1(X5,X6,X7,X4)
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X5 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X5,X6,X7))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_40,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k7_mcart_1(X5,X6,X7,X4)
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X5 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X5,X6,X7))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_42,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k6_mcart_1(X5,X6,X7,X4)
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X5 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X5,X6,X7))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk8_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( k5_mcart_1(X1,X2,X3,esk7_0) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk7_0) = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k6_mcart_1(X1,X2,X3,esk7_0) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk8_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_36])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk8_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_56,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_57,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0)
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

fof(c_0_63,plain,(
    ! [X36,X37,X38] :
      ( ( X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | k3_zfmisc_1(X36,X37,X38) != k1_xboole_0 )
      & ( X36 != k1_xboole_0
        | k3_zfmisc_1(X36,X37,X38) = k1_xboole_0 )
      & ( X37 != k1_xboole_0
        | k3_zfmisc_1(X36,X37,X38) = k1_xboole_0 )
      & ( X38 != k1_xboole_0
        | k3_zfmisc_1(X36,X37,X38) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_64,plain,
    ( esk8_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk4_0)
    | ~ r2_hidden(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk5_0)
    | ~ r2_hidden(k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(k7_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( esk8_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_73,plain,
    ( k3_zfmisc_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_71]),c_0_65])])).

cnf(c_0_75,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_76,plain,(
    ! [X58,X59] :
      ( ~ v1_xboole_0(X58)
      | X58 = X59
      | ~ v1_xboole_0(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_78,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_72]),c_0_73]),c_0_74])).

cnf(c_0_79,plain,
    ( k3_zfmisc_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_80,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_81,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_48])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_78]),c_0_79]),c_0_74])).

cnf(c_0_86,plain,
    ( k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_88,plain,
    ( X1 = X2
    | r2_hidden(esk8_1(X2),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_45])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(esk1_0)
    | r2_hidden(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_54])).

cnf(c_0_92,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_85]),c_0_86]),c_0_74])).

fof(c_0_93,plain,(
    ! [X56,X57] :
      ( ~ r2_hidden(X56,X57)
      | ~ v1_xboole_0(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( esk1_0 = X1
    | r2_hidden(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk1_0)
    | r2_hidden(esk8_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,plain,
    ( m1_subset_1(k7_mcart_1(X1,k1_xboole_0,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_79])).

cnf(c_0_97,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_54])).

cnf(c_0_98,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_65])])).

cnf(c_0_99,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 = esk1_0
    | r2_hidden(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk7_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_89])).

cnf(c_0_101,plain,
    ( m1_subset_1(k7_mcart_1(X1,k1_xboole_0,X2,esk8_1(k1_xboole_0)),X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_36])).

cnf(c_0_102,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk8_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_45])).

cnf(c_0_103,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_98]),c_0_73]),c_0_74])).

cnf(c_0_104,plain,
    ( m1_subset_1(k5_mcart_1(X1,X2,X3,esk8_1(k3_zfmisc_1(X1,X2,X3))),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_105,negated_conjecture,
    ( esk4_0 = esk1_0
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(k7_mcart_1(X2,k1_xboole_0,X1,esk8_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_74])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_xboole_0(k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_20])).

cnf(c_0_109,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(k5_mcart_1(X1,X2,X3,esk8_1(k3_zfmisc_1(X1,X2,X3))),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( esk4_0 = esk1_0
    | r2_hidden(k7_mcart_1(X1,k1_xboole_0,esk1_0,esk8_1(k1_xboole_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_107]),c_0_79]),c_0_74])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(k5_mcart_1(k3_zfmisc_1(esk4_0,esk5_0,esk6_0),X1,X2,esk8_1(k3_zfmisc_1(k3_zfmisc_1(esk4_0,esk5_0,esk6_0),X1,X2))),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_111]),c_0_111]),c_0_74])).

cnf(c_0_114,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113]),c_0_86]),c_0_113]),c_0_86]),c_0_86]),c_0_113]),c_0_86]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------
