%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t15_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 226.05s
% Output     : CNFRefutation 226.05s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 362 expanded)
%              Number of clauses        :   54 ( 156 expanded)
%              Number of leaves         :    8 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  257 (2220 expanded)
%              Number of equality atoms :   32 ( 244 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',d3_xboole_0)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',t7_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',dt_k4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',redefinition_k4_subset_1)).

fof(t15_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        | r2_hidden(X5,X4) ) ) )
               => X2 = k4_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',t15_subset_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',idempotence_k2_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',commutativity_k2_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',d10_xboole_0)).

fof(c_0_8,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X26)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X27)
        | r2_hidden(esk5_3(X25,X26,X27),X25)
        | r2_hidden(esk5_3(X25,X26,X27),X26)
        | X27 = k2_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X45,X46,X47] :
      ( ( m1_subset_1(esk7_3(X45,X46,X47),X45)
        | r1_tarski(X46,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) )
      & ( r2_hidden(esk7_3(X45,X46,X47),X46)
        | r1_tarski(X46,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) )
      & ( ~ r2_hidden(esk7_3(X45,X46,X47),X47)
        | r1_tarski(X46,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | ~ m1_subset_1(X31,k1_zfmisc_1(X29))
      | m1_subset_1(k4_subset_1(X29,X30,X31),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_14,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | ~ m1_subset_1(X40,k1_zfmisc_1(X38))
      | k4_subset_1(X38,X39,X40) = k2_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk7_3(X4,X1,k2_xboole_0(X2,X3)),X3)
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,X2)
                      <=> ( r2_hidden(X5,X3)
                          | r2_hidden(X5,X4) ) ) )
                 => X2 = k4_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_subset_1])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ m1_subset_1(k2_xboole_0(X2,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X3)
    | r2_hidden(esk7_3(X4,k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk7_3(X4,k2_xboole_0(X1,X2),X3),X1)
    | ~ m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

fof(c_0_25,negated_conjecture,(
    ! [X10] :
      ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
      & ( ~ r2_hidden(X10,esk2_0)
        | r2_hidden(X10,esk3_0)
        | r2_hidden(X10,esk4_0)
        | ~ m1_subset_1(X10,esk1_0) )
      & ( ~ r2_hidden(X10,esk3_0)
        | r2_hidden(X10,esk2_0)
        | ~ m1_subset_1(X10,esk1_0) )
      & ( ~ r2_hidden(X10,esk4_0)
        | r2_hidden(X10,esk2_0)
        | ~ m1_subset_1(X10,esk1_0) )
      & esk2_0 != k4_subset_1(esk1_0,esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X3)
    | r2_hidden(esk7_3(X4,k2_xboole_0(X1,X2),X3),X1)
    | r2_hidden(esk7_3(X4,k2_xboole_0(X1,X2),X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,k2_xboole_0(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X34] : k2_xboole_0(X34,X34) = X34 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,X2),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(X1,X2),esk2_0),X2)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(X1,X2),esk2_0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(esk4_0,k2_xboole_0(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k2_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk4_0),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(X1,esk4_0),esk2_0),esk4_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(X1,esk4_0),esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

fof(c_0_39,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk7_3(esk1_0,X1,X2),esk2_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,X2),esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,esk4_0),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk2_0,esk4_0),esk2_0),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk2_0,esk4_0),esk2_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X1,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,esk4_0),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk2_0,esk4_0),esk2_0),esk2_0)
    | ~ m1_subset_1(k2_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28])])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk7_3(esk1_0,X1,X2),esk4_0)
    | r2_hidden(esk7_3(esk1_0,X1,X2),esk3_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,X2),esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(X1,esk4_0) = X1
    | ~ r1_tarski(k2_xboole_0(X1,esk4_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k2_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_48]),c_0_28])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk7_3(X4,X1,k2_xboole_0(X2,X3)),X2)
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X2,esk4_0))
    | r2_hidden(esk7_3(esk1_0,X1,k2_xboole_0(X2,esk4_0)),esk3_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,k2_xboole_0(X2,esk4_0)),esk2_0)
    | ~ m1_subset_1(k2_xboole_0(X2,esk4_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0
    | ~ m1_subset_1(k2_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_28])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))
    | ~ r2_hidden(esk7_3(esk1_0,X1,k2_xboole_0(esk3_0,esk4_0)),esk2_0)
    | ~ m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 != k4_subset_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_23]),c_0_30]),c_0_28])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_17]),c_0_28])])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_19]),c_0_30]),c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r2_hidden(esk7_3(X2,X1,esk2_0),esk4_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk3_0,esk4_0),esk2_0),esk3_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk3_0,esk4_0),esk2_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_60]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk7_3(esk1_0,X1,X2),esk2_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,X2),esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_37])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk3_0,esk4_0),esk2_0),esk3_0)
    | ~ m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_28])]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0)
    | ~ m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_28])]),c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_68]),c_0_28])]),c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_23]),c_0_30]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
