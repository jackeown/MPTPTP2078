%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:37 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 394 expanded)
%              Number of clauses        :   41 ( 164 expanded)
%              Number of leaves         :   12 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 (2320 expanded)
%              Number of equality atoms :   18 ( 185 expanded)
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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc4_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v4_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X49,X50] :
      ( ( ~ m1_subset_1(X50,X49)
        | r2_hidden(X50,X49)
        | v1_xboole_0(X49) )
      & ( ~ r2_hidden(X50,X49)
        | m1_subset_1(X50,X49)
        | v1_xboole_0(X49) )
      & ( ~ m1_subset_1(X50,X49)
        | v1_xboole_0(X50)
        | ~ v1_xboole_0(X49) )
      & ( ~ v1_xboole_0(X50)
        | m1_subset_1(X50,X49)
        | ~ v1_xboole_0(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X72] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
      & ( v3_pre_topc(X72,esk2_0)
        | ~ r2_hidden(X72,esk4_0)
        | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( v4_pre_topc(X72,esk2_0)
        | ~ r2_hidden(X72,esk4_0)
        | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( r2_hidden(esk3_0,X72)
        | ~ r2_hidden(X72,esk4_0)
        | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( ~ v3_pre_topc(X72,esk2_0)
        | ~ v4_pre_topc(X72,esk2_0)
        | ~ r2_hidden(esk3_0,X72)
        | r2_hidden(X72,esk4_0)
        | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & esk4_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_15,plain,(
    ! [X62,X63] :
      ( ~ r2_hidden(X62,X63)
      | ~ r1_tarski(X63,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_16,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_17,plain,(
    ! [X66] :
      ( v2_struct_0(X66)
      | ~ l1_struct_0(X66)
      | ~ v1_xboole_0(u1_struct_0(X66)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X68] :
      ( ~ v2_pre_topc(X68)
      | ~ l1_pre_topc(X68)
      | v3_pre_topc(k2_struct_0(X68),X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

fof(c_0_25,plain,(
    ! [X64] :
      ( ~ l1_struct_0(X64)
      | k2_struct_0(X64) = u1_struct_0(X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_26,plain,(
    ! [X65] :
      ( ~ l1_pre_topc(X65)
      | l1_struct_0(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ( ~ r2_hidden(X44,X43)
        | r1_tarski(X44,X42)
        | X43 != k1_zfmisc_1(X42) )
      & ( ~ r1_tarski(X45,X42)
        | r2_hidden(X45,X43)
        | X43 != k1_zfmisc_1(X42) )
      & ( ~ r2_hidden(esk1_2(X46,X47),X47)
        | ~ r1_tarski(esk1_2(X46,X47),X46)
        | X47 = k1_zfmisc_1(X46) )
      & ( r2_hidden(esk1_2(X46,X47),X47)
        | r1_tarski(esk1_2(X46,X47),X46)
        | X47 = k1_zfmisc_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_31,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_39,plain,(
    ! [X67] :
      ( ~ v2_pre_topc(X67)
      | ~ l1_pre_topc(X67)
      | v4_pre_topc(k2_struct_0(X67),X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(sr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_38])])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( ~ v4_pre_topc(u1_struct_0(esk2_0),esk2_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_38])])).

cnf(c_0_50,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_36])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_45]),c_0_38])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_55,plain,(
    ! [X59,X60,X61] :
      ( ~ r2_hidden(X59,X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(X61))
      | m1_subset_1(X59,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_59])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_62]),c_0_63]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:09:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.018 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.14/0.37  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.14/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.37  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.14/0.37  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.14/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.37  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.14/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.14/0.37  fof(c_0_13, plain, ![X49, X50]:(((~m1_subset_1(X50,X49)|r2_hidden(X50,X49)|v1_xboole_0(X49))&(~r2_hidden(X50,X49)|m1_subset_1(X50,X49)|v1_xboole_0(X49)))&((~m1_subset_1(X50,X49)|v1_xboole_0(X50)|~v1_xboole_0(X49))&(~v1_xboole_0(X50)|m1_subset_1(X50,X49)|~v1_xboole_0(X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.14/0.37  fof(c_0_14, negated_conjecture, ![X72]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(((((v3_pre_topc(X72,esk2_0)|~r2_hidden(X72,esk4_0)|~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(esk2_0))))&(v4_pre_topc(X72,esk2_0)|~r2_hidden(X72,esk4_0)|~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(esk2_0)))))&(r2_hidden(esk3_0,X72)|~r2_hidden(X72,esk4_0)|~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(esk2_0)))))&(~v3_pre_topc(X72,esk2_0)|~v4_pre_topc(X72,esk2_0)|~r2_hidden(esk3_0,X72)|r2_hidden(X72,esk4_0)|~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(esk2_0)))))&esk4_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.14/0.37  fof(c_0_15, plain, ![X62, X63]:(~r2_hidden(X62,X63)|~r1_tarski(X63,X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.37  fof(c_0_16, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.37  fof(c_0_17, plain, ![X66]:(v2_struct_0(X66)|~l1_struct_0(X66)|~v1_xboole_0(u1_struct_0(X66))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.37  cnf(c_0_18, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk4_0)|~v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~r2_hidden(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (esk4_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_23, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.37  fof(c_0_24, plain, ![X68]:(~v2_pre_topc(X68)|~l1_pre_topc(X68)|v3_pre_topc(k2_struct_0(X68),X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.14/0.37  fof(c_0_25, plain, ![X64]:(~l1_struct_0(X64)|k2_struct_0(X64)=u1_struct_0(X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.14/0.37  fof(c_0_26, plain, ![X65]:(~l1_pre_topc(X65)|l1_struct_0(X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.37  cnf(c_0_27, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  fof(c_0_30, plain, ![X42, X43, X44, X45, X46, X47]:(((~r2_hidden(X44,X43)|r1_tarski(X44,X42)|X43!=k1_zfmisc_1(X42))&(~r1_tarski(X45,X42)|r2_hidden(X45,X43)|X43!=k1_zfmisc_1(X42)))&((~r2_hidden(esk1_2(X46,X47),X47)|~r1_tarski(esk1_2(X46,X47),X46)|X47=k1_zfmisc_1(X46))&(r2_hidden(esk1_2(X46,X47),X47)|r1_tarski(esk1_2(X46,X47),X46)|X47=k1_zfmisc_1(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.37  fof(c_0_31, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.37  cnf(c_0_33, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.37  cnf(c_0_34, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_35, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.37  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_0,u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.14/0.37  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  fof(c_0_39, plain, ![X67]:(~v2_pre_topc(X67)|~l1_pre_topc(X67)|v4_pre_topc(k2_struct_0(X67),X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.14/0.37  cnf(c_0_40, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.37  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (~v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)), inference(sr,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.37  cnf(c_0_43, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_38])])).
% 0.14/0.37  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_46, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.37  cnf(c_0_47, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_40])).
% 0.14/0.37  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.14/0.37  cnf(c_0_49, negated_conjecture, (~v4_pre_topc(u1_struct_0(esk2_0),esk2_0)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_38])])).
% 0.14/0.37  cnf(c_0_50, plain, (v4_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_35]), c_0_36])).
% 0.14/0.37  cnf(c_0_51, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_52, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.37  cnf(c_0_53, negated_conjecture, (~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_45]), c_0_38])])).
% 0.14/0.37  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.37  fof(c_0_55, plain, ![X59, X60, X61]:(~r2_hidden(X59,X60)|~m1_subset_1(X60,k1_zfmisc_1(X61))|m1_subset_1(X59,X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.37  cnf(c_0_56, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_57, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.14/0.37  cnf(c_0_58, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.14/0.37  cnf(c_0_59, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.37  cnf(c_0_60, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.14/0.37  cnf(c_0_61, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_52])).
% 0.14/0.37  cnf(c_0_62, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_57])).
% 0.14/0.37  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_59])).
% 0.14/0.37  cnf(c_0_64, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_22, c_0_48])).
% 0.14/0.37  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_62]), c_0_63]), c_0_64]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 66
% 0.14/0.37  # Proof object clause steps            : 41
% 0.14/0.37  # Proof object formula steps           : 25
% 0.14/0.37  # Proof object conjectures             : 23
% 0.14/0.37  # Proof object clause conjectures      : 20
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 19
% 0.14/0.37  # Proof object initial formulas used   : 12
% 0.14/0.37  # Proof object generating inferences   : 18
% 0.14/0.37  # Proof object simplifying inferences  : 18
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 25
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 42
% 0.14/0.37  # Removed in clause preprocessing      : 8
% 0.14/0.37  # Initial clauses in saturation        : 34
% 0.14/0.37  # Processed clauses                    : 111
% 0.14/0.37  # ...of these trivial                  : 2
% 0.14/0.37  # ...subsumed                          : 8
% 0.14/0.37  # ...remaining for further processing  : 101
% 0.14/0.37  # Other redundant clauses eliminated   : 4
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 1
% 0.14/0.37  # Backward-rewritten                   : 7
% 0.14/0.37  # Generated clauses                    : 86
% 0.14/0.37  # ...of the previous two non-trivial   : 70
% 0.14/0.37  # Contextual simplify-reflections      : 2
% 0.14/0.37  # Paramodulations                      : 82
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 4
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 57
% 0.14/0.37  #    Positive orientable unit clauses  : 18
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 5
% 0.14/0.37  #    Non-unit-clauses                  : 34
% 0.14/0.37  # Current number of unprocessed clauses: 22
% 0.14/0.37  # ...number of literals in the above   : 70
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 48
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 275
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 148
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.37  # Unit Clause-clause subsumption calls : 22
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 10
% 0.14/0.37  # BW rewrite match successes           : 5
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 3797
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.021 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.024 s
% 0.14/0.37  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
