%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1399+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   52 (  99 expanded)
%              Number of clauses        :   29 (  40 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 596 expanded)
%              Number of equality atoms :   11 (  45 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r2_hidden(X4,X3)
                      <=> ( v3_pre_topc(X4,X1)
                          & v4_pre_topc(X4,X1)
                          & r2_hidden(X2,X4) ) ) )
                  & X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT009+2.ax',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',dt_l1_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',d3_struct_0)).

fof(fc4_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v4_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',fc4_pre_topc)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT019+2.ax',fc10_tops_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d2_subset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X4,X3)
                        <=> ( v3_pre_topc(X4,X1)
                            & v4_pre_topc(X4,X1)
                            & r2_hidden(X2,X4) ) ) )
                    & X3 = k1_xboole_0 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_connsp_2])).

fof(c_0_12,negated_conjecture,(
    ! [X7903] :
      ( ~ v2_struct_0(esk831_0)
      & v2_pre_topc(esk831_0)
      & l1_pre_topc(esk831_0)
      & m1_subset_1(esk832_0,u1_struct_0(esk831_0))
      & m1_subset_1(esk833_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk831_0))))
      & ( v3_pre_topc(X7903,esk831_0)
        | ~ r2_hidden(X7903,esk833_0)
        | ~ m1_subset_1(X7903,k1_zfmisc_1(u1_struct_0(esk831_0))) )
      & ( v4_pre_topc(X7903,esk831_0)
        | ~ r2_hidden(X7903,esk833_0)
        | ~ m1_subset_1(X7903,k1_zfmisc_1(u1_struct_0(esk831_0))) )
      & ( r2_hidden(esk832_0,X7903)
        | ~ r2_hidden(X7903,esk833_0)
        | ~ m1_subset_1(X7903,k1_zfmisc_1(u1_struct_0(esk831_0))) )
      & ( ~ v3_pre_topc(X7903,esk831_0)
        | ~ v4_pre_topc(X7903,esk831_0)
        | ~ r2_hidden(esk832_0,X7903)
        | r2_hidden(X7903,esk833_0)
        | ~ m1_subset_1(X7903,k1_zfmisc_1(u1_struct_0(esk831_0))) )
      & esk833_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

fof(c_0_13,plain,(
    ! [X3335,X3336] :
      ( ~ r2_hidden(X3335,X3336)
      | ~ r1_tarski(X3336,X3335) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_14,plain,(
    ! [X247] : r1_tarski(k1_xboole_0,X247) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_15,plain,(
    ! [X5917] :
      ( ~ l1_pre_topc(X5917)
      | l1_struct_0(X5917) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk833_0)
    | ~ v3_pre_topc(X1,esk831_0)
    | ~ v4_pre_topc(X1,esk831_0)
    | ~ r2_hidden(esk832_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk831_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk833_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X1583] : m1_subset_1(k2_subset_1(X1583),k1_zfmisc_1(X1583)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_21,plain,(
    ! [X1539] : k2_subset_1(X1539) = X1539 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_22,plain,(
    ! [X5896] :
      ( ~ l1_struct_0(X5896)
      | k2_struct_0(X5896) = u1_struct_0(X5896) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_23,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk831_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v3_pre_topc(X1,esk831_0)
    | ~ v4_pre_topc(X1,esk831_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk831_0)))
    | ~ r2_hidden(esk832_0,X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X5936] :
      ( ~ v2_pre_topc(X5936)
      | ~ l1_pre_topc(X5936)
      | v4_pre_topc(k2_struct_0(X5936),X5936) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

cnf(c_0_30,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( l1_struct_0(esk831_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk831_0)
    | ~ v4_pre_topc(X1,esk831_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk831_0)))
    | ~ r2_hidden(esk832_0,X1) ),
    inference(sr,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k2_struct_0(esk831_0) = u1_struct_0(esk831_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk831_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_37,plain,(
    ! [X6770] :
      ( ~ v2_pre_topc(X6770)
      | ~ l1_pre_topc(X6770)
      | v3_pre_topc(k2_struct_0(X6770),X6770) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

fof(c_0_38,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_39,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk831_0),esk831_0)
    | ~ v4_pre_topc(u1_struct_0(esk831_0),esk831_0)
    | ~ r2_hidden(esk832_0,u1_struct_0(esk831_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v4_pre_topc(u1_struct_0(esk831_0),esk831_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_35]),c_0_36])])).

cnf(c_0_41,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_42,plain,(
    ! [X1504,X1505] :
      ( ( ~ m1_subset_1(X1505,X1504)
        | r2_hidden(X1505,X1504)
        | v1_xboole_0(X1504) )
      & ( ~ r2_hidden(X1505,X1504)
        | m1_subset_1(X1505,X1504)
        | v1_xboole_0(X1504) )
      & ( ~ m1_subset_1(X1505,X1504)
        | v1_xboole_0(X1505)
        | ~ v1_xboole_0(X1504) )
      & ( ~ v1_xboole_0(X1505)
        | m1_subset_1(X1505,X1504)
        | ~ v1_xboole_0(X1504) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk831_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk831_0),esk831_0)
    | ~ r2_hidden(esk832_0,u1_struct_0(esk831_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk831_0),esk831_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_35]),c_0_36])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk832_0,u1_struct_0(esk831_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk831_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_31]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk832_0,u1_struct_0(esk831_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
