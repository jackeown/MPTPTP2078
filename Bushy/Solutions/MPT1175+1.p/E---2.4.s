%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t82_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:23 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 107 expanded)
%              Number of clauses        :   21 (  40 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 543 expanded)
%              Number of equality atoms :    7 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_orders_1,axiom,(
    ! [X1] : k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t82_orders_2.p',d2_orders_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t82_orders_2.p',redefinition_k9_setfam_1)).

fof(t82_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X2)
                 => ~ r1_xboole_0(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t82_orders_2.p',t82_orders_2)).

fof(t79_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t82_orders_2.p',t79_orders_2)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t82_orders_2.p',t3_xboole_0)).

fof(c_0_5,plain,(
    ! [X11] : k1_orders_1(X11) = k7_subset_1(k1_zfmisc_1(X11),k9_setfam_1(X11),k1_tarski(k1_xboole_0)) ),
    inference(variable_rename,[status(thm)],[d2_orders_1])).

fof(c_0_6,plain,(
    ! [X34] : k9_setfam_1(X34) = k1_zfmisc_1(X34) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m2_orders_2(X3,X1,X2)
               => ! [X4] :
                    ( m2_orders_2(X4,X1,X2)
                   => ~ r1_xboole_0(X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t82_orders_2])).

fof(c_0_8,plain,(
    ! [X58,X59,X60] :
      ( v2_struct_0(X58)
      | ~ v3_orders_2(X58)
      | ~ v4_orders_2(X58)
      | ~ v5_orders_2(X58)
      | ~ l1_orders_2(X58)
      | ~ m1_orders_1(X59,k1_orders_1(u1_struct_0(X58)))
      | ~ m2_orders_2(X60,X58,X59)
      | r2_hidden(k1_funct_1(X59,u1_struct_0(X58)),X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).

cnf(c_0_9,plain,
    ( k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0)))
    & m2_orders_2(esk3_0,esk1_0,esk2_0)
    & m2_orders_2(esk4_0,esk1_0,esk2_0)
    & r1_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(X1),k1_tarski(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X44,X45,X47,X48,X49] :
      ( ( r2_hidden(esk10_2(X44,X45),X44)
        | r1_xboole_0(X44,X45) )
      & ( r2_hidden(esk10_2(X44,X45),X45)
        | r1_xboole_0(X44,X45) )
      & ( ~ r2_hidden(X49,X47)
        | ~ r2_hidden(X49,X48)
        | ~ r1_xboole_0(X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_orders_1(esk2_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,u1_struct_0(esk1_0)),X1)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk2_0,u1_struct_0(esk1_0)),X1)
    | ~ r1_xboole_0(X1,X2)
    | ~ m2_orders_2(X2,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_xboole_0(X1,X2)
    | ~ m2_orders_2(X2,esk1_0,esk2_0)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( m2_orders_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_xboole_0(X1,esk4_0)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( m2_orders_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
