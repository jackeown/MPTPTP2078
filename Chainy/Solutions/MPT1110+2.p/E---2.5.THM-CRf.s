%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1110+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:02 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   46 (  78 expanded)
%              Number of clauses        :   27 (  33 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 ( 274 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t79_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',d1_zfmisc_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t4_subset)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_pre_topc])).

fof(c_0_10,plain,(
    ! [X263,X264] :
      ( ~ l1_pre_topc(X263)
      | ~ m1_pre_topc(X264,X263)
      | l1_pre_topc(X264) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X277] :
      ( ~ l1_pre_topc(X277)
      | l1_struct_0(X277) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_13,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X215,X216,X217,X219,X221] :
      ( ( r1_tarski(k2_struct_0(X216),k2_struct_0(X215))
        | ~ m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) )
      & ( m1_subset_1(esk22_3(X215,X216,X217),k1_zfmisc_1(u1_struct_0(X215)))
        | ~ r2_hidden(X217,u1_pre_topc(X216))
        | ~ m1_subset_1(X217,k1_zfmisc_1(u1_struct_0(X216)))
        | ~ m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) )
      & ( r2_hidden(esk22_3(X215,X216,X217),u1_pre_topc(X215))
        | ~ r2_hidden(X217,u1_pre_topc(X216))
        | ~ m1_subset_1(X217,k1_zfmisc_1(u1_struct_0(X216)))
        | ~ m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) )
      & ( X217 = k9_subset_1(u1_struct_0(X216),esk22_3(X215,X216,X217),k2_struct_0(X216))
        | ~ r2_hidden(X217,u1_pre_topc(X216))
        | ~ m1_subset_1(X217,k1_zfmisc_1(u1_struct_0(X216)))
        | ~ m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) )
      & ( ~ m1_subset_1(X219,k1_zfmisc_1(u1_struct_0(X215)))
        | ~ r2_hidden(X219,u1_pre_topc(X215))
        | X217 != k9_subset_1(u1_struct_0(X216),X219,k2_struct_0(X216))
        | r2_hidden(X217,u1_pre_topc(X216))
        | ~ m1_subset_1(X217,k1_zfmisc_1(u1_struct_0(X216)))
        | ~ m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) )
      & ( m1_subset_1(esk23_2(X215,X216),k1_zfmisc_1(u1_struct_0(X216)))
        | ~ r1_tarski(k2_struct_0(X216),k2_struct_0(X215))
        | m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) )
      & ( ~ r2_hidden(esk23_2(X215,X216),u1_pre_topc(X216))
        | ~ m1_subset_1(X221,k1_zfmisc_1(u1_struct_0(X215)))
        | ~ r2_hidden(X221,u1_pre_topc(X215))
        | esk23_2(X215,X216) != k9_subset_1(u1_struct_0(X216),X221,k2_struct_0(X216))
        | ~ r1_tarski(k2_struct_0(X216),k2_struct_0(X215))
        | m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) )
      & ( m1_subset_1(esk24_2(X215,X216),k1_zfmisc_1(u1_struct_0(X215)))
        | r2_hidden(esk23_2(X215,X216),u1_pre_topc(X216))
        | ~ r1_tarski(k2_struct_0(X216),k2_struct_0(X215))
        | m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) )
      & ( r2_hidden(esk24_2(X215,X216),u1_pre_topc(X215))
        | r2_hidden(esk23_2(X215,X216),u1_pre_topc(X216))
        | ~ r1_tarski(k2_struct_0(X216),k2_struct_0(X215))
        | m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) )
      & ( esk23_2(X215,X216) = k9_subset_1(u1_struct_0(X216),esk24_2(X215,X216),k2_struct_0(X216))
        | r2_hidden(esk23_2(X215,X216),u1_pre_topc(X216))
        | ~ r1_tarski(k2_struct_0(X216),k2_struct_0(X215))
        | m1_pre_topc(X216,X215)
        | ~ l1_pre_topc(X216)
        | ~ l1_pre_topc(X215) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_17,plain,(
    ! [X214] :
      ( ~ l1_struct_0(X214)
      | k2_struct_0(X214) = u1_struct_0(X214) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_18,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

fof(c_0_24,plain,(
    ! [X194,X195] :
      ( ~ r1_tarski(X194,X195)
      | r1_tarski(k1_zfmisc_1(X194),k1_zfmisc_1(X195)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

fof(c_0_28,plain,(
    ! [X73,X74] :
      ( ( ~ m1_subset_1(X73,k1_zfmisc_1(X74))
        | r1_tarski(X73,X74) )
      & ( ~ r1_tarski(X73,X74)
        | m1_subset_1(X73,k1_zfmisc_1(X74)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_26]),c_0_27]),c_0_15])])).

fof(c_0_31,plain,(
    ! [X184,X185,X186,X187,X188,X189] :
      ( ( ~ r2_hidden(X186,X185)
        | r1_tarski(X186,X184)
        | X185 != k1_zfmisc_1(X184) )
      & ( ~ r1_tarski(X187,X184)
        | r2_hidden(X187,X185)
        | X185 != k1_zfmisc_1(X184) )
      & ( ~ r2_hidden(esk18_2(X188,X189),X189)
        | ~ r1_tarski(esk18_2(X188,X189),X188)
        | X189 = k1_zfmisc_1(X188) )
      & ( r2_hidden(esk18_2(X188,X189),X189)
        | r1_tarski(esk18_2(X188,X189),X188)
        | X189 = k1_zfmisc_1(X188) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_32,plain,(
    ! [X79,X80,X81] :
      ( ~ r2_hidden(X79,X80)
      | ~ m1_subset_1(X80,k1_zfmisc_1(X81))
      | m1_subset_1(X79,X81) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(u1_struct_0(esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
