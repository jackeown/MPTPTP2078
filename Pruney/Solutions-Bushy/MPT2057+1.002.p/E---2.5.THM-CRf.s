%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2057+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 438 expanded)
%              Number of clauses        :   44 ( 146 expanded)
%              Number of leaves         :   10 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  257 (3245 expanded)
%              Number of equality atoms :   21 (  43 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   27 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
             => ( r2_hidden(X3,X2)
              <=> r1_waybel_0(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow19)).

fof(t14_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(t11_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_hidden(X3,k2_yellow19(X1,X2))
            <=> ( r1_waybel_0(X1,X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow19)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k3_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & ~ v1_xboole_0(X3)
        & v2_waybel_0(X3,k3_yellow_1(X2))
        & v13_waybel_0(X3,k3_yellow_1(X2))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) )
     => ( ~ v2_struct_0(k3_yellow19(X1,X2,X3))
        & v6_waybel_0(k3_yellow19(X1,X2,X3),X1)
        & l1_waybel_0(k3_yellow19(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
               => ( r2_hidden(X3,X2)
                <=> r1_waybel_0(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_yellow19])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ l1_struct_0(X15)
      | v1_xboole_0(X16)
      | ~ v2_waybel_0(X16,k3_yellow_1(k2_struct_0(X15)))
      | ~ v13_waybel_0(X16,k3_yellow_1(k2_struct_0(X15)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X15)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X15))),X16,k1_tarski(k1_xboole_0)) = k2_yellow19(X15,k3_yellow19(X15,k2_struct_0(X15),X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))
    & ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ r2_hidden(esk3_0,esk2_0)
      | ~ r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) )
    & ( r2_hidden(esk3_0,esk2_0)
      | r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ( r1_waybel_0(X12,X13,X14)
        | ~ r2_hidden(X14,k2_yellow19(X12,X13))
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X14,k2_yellow19(X12,X13))
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( ~ r1_waybel_0(X12,X13,X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | r2_hidden(X14,k2_yellow19(X12,X13))
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t11_yellow19])])])])])).

fof(c_0_14,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k7_subset_1(X9,X10,X11) = k4_xboole_0(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v2_struct_0(k3_yellow19(X5,X6,X7))
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5)
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v1_xboole_0(X7)
        | ~ v2_waybel_0(X7,k3_yellow_1(X6))
        | ~ v13_waybel_0(X7,k3_yellow_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X6)))) )
      & ( v6_waybel_0(k3_yellow19(X5,X6,X7),X5)
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5)
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v1_xboole_0(X7)
        | ~ v2_waybel_0(X7,k3_yellow_1(X6))
        | ~ v13_waybel_0(X7,k3_yellow_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X6)))) )
      & ( l1_waybel_0(k3_yellow19(X5,X6,X7),X5)
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5)
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v1_xboole_0(X7)
        | ~ v2_waybel_0(X7,k3_yellow_1(X6))
        | ~ v13_waybel_0(X7,k3_yellow_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X6)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,k2_yellow19(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))),esk2_0,k1_tarski(k1_xboole_0)) = k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

fof(c_0_27,plain,(
    ! [X17,X18,X19] :
      ( ( r2_hidden(X17,X18)
        | ~ r2_hidden(X17,k4_xboole_0(X18,k1_tarski(X19))) )
      & ( X17 != X19
        | ~ r2_hidden(X17,k4_xboole_0(X18,k1_tarski(X19))) )
      & ( ~ r2_hidden(X17,X18)
        | X17 = X19
        | r2_hidden(X17,k4_xboole_0(X18,k1_tarski(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_28,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | m1_subset_1(k2_struct_0(X4),k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,k2_yellow19(esk1_0,X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk1_0,X1,esk3_0)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19])]),c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) = k4_xboole_0(esk2_0,k1_tarski(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_16])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19])]),c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_41,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(k2_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_19])]),c_0_21])).

cnf(c_0_43,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_19])])).

cnf(c_0_46,negated_conjecture,
    ( r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r2_hidden(X1,k4_xboole_0(esk2_0,k1_tarski(k1_xboole_0)))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_32]),c_0_19])]),c_0_21])).

cnf(c_0_47,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_19])]),c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0)
    | ~ r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r2_hidden(X1,k4_xboole_0(esk2_0,k1_tarski(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( esk3_0 = X1
    | r2_hidden(esk3_0,k4_xboole_0(esk2_0,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

fof(c_0_54,plain,(
    ! [X20] :
      ( ~ v1_xboole_0(X20)
      | X20 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_53]),c_0_19])]),c_0_21])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_57,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_58,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_35]),c_0_19])])).

cnf(c_0_59,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_58]),c_0_19])]),c_0_21])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])]),
    [proof]).

%------------------------------------------------------------------------------
