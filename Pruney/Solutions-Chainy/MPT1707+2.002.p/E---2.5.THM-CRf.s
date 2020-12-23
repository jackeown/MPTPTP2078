%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 220 expanded)
%              Number of clauses        :   41 (  75 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  311 (1899 expanded)
%              Number of equality atoms :   27 ( 240 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                 => ~ ( ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => X5 != X4 )
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => X5 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d2_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_pre_topc(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( X4 = k1_tsep_1(X1,X2,X3)
                  <=> u1_struct_0(X4) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t30_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                   => ~ ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => X5 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => X5 != X4 ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_tmap_1])).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_13,negated_conjecture,(
    ! [X41,X42] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X41,u1_struct_0(esk3_0))
        | X41 != esk5_0 )
      & ( ~ m1_subset_1(X42,u1_struct_0(esk4_0))
        | X42 != esk5_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_14,plain,(
    ! [X30,X31,X32,X33] :
      ( ( X33 != k1_tsep_1(X30,X31,X32)
        | u1_struct_0(X33) = k2_xboole_0(u1_struct_0(X31),u1_struct_0(X32))
        | v2_struct_0(X33)
        | ~ v1_pre_topc(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30) )
      & ( u1_struct_0(X33) != k2_xboole_0(u1_struct_0(X31),u1_struct_0(X32))
        | X33 = k1_tsep_1(X30,X31,X32)
        | v2_struct_0(X33)
        | ~ v1_pre_topc(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

fof(c_0_15,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v2_struct_0(k1_tsep_1(X34,X35,X36))
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X34) )
      & ( v1_pre_topc(k1_tsep_1(X34,X35,X36))
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X34) )
      & ( m1_pre_topc(k1_tsep_1(X34,X35,X36),X34)
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | m1_subset_1(k1_connsp_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_18,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( u1_struct_0(X1) = k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k1_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | r2_hidden(X29,k1_connsp_2(X28,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).

fof(c_0_28,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))
    | r2_hidden(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_31,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X3,k1_connsp_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_connsp_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | X1 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))
    | r2_hidden(esk5_0,k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | X1 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( X1 != esk5_0
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))
    | r2_hidden(esk5_0,u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ v2_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( X1 != esk5_0
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))
    | r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_51,plain,(
    ! [X22,X23] :
      ( ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | v2_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_52,negated_conjecture,
    ( v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ v2_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_55,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | l1_pre_topc(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ v2_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_pre_topc(k1_tsep_1(X1,X2,X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_32]),c_0_33]),c_0_34]),c_0_58])]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | l1_pre_topc(k1_tsep_1(X1,X2,X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_32]),c_0_33]),c_0_34])]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_62]),c_0_32]),c_0_33]),c_0_34])]),c_0_37]),c_0_36]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:07:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t16_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))=>~((![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>X5!=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X3))=>X5!=X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tmap_1)).
% 0.19/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.37  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.19/0.37  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.19/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.37  fof(dt_k1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 0.19/0.37  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.37  fof(t30_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r2_hidden(X2,k1_connsp_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 0.19/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.37  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.37  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))=>~((![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>X5!=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X3))=>X5!=X4)))))))), inference(assume_negation,[status(cth)],[t16_tmap_1])).
% 0.19/0.37  fof(c_0_12, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.37  fof(c_0_13, negated_conjecture, ![X41, X42]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))&((~m1_subset_1(X41,u1_struct_0(esk3_0))|X41!=esk5_0)&(~m1_subset_1(X42,u1_struct_0(esk4_0))|X42!=esk5_0)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X30, X31, X32, X33]:((X33!=k1_tsep_1(X30,X31,X32)|u1_struct_0(X33)=k2_xboole_0(u1_struct_0(X31),u1_struct_0(X32))|(v2_struct_0(X33)|~v1_pre_topc(X33)|~m1_pre_topc(X33,X30))|(v2_struct_0(X32)|~m1_pre_topc(X32,X30))|(v2_struct_0(X31)|~m1_pre_topc(X31,X30))|(v2_struct_0(X30)|~l1_pre_topc(X30)))&(u1_struct_0(X33)!=k2_xboole_0(u1_struct_0(X31),u1_struct_0(X32))|X33=k1_tsep_1(X30,X31,X32)|(v2_struct_0(X33)|~v1_pre_topc(X33)|~m1_pre_topc(X33,X30))|(v2_struct_0(X32)|~m1_pre_topc(X32,X30))|(v2_struct_0(X31)|~m1_pre_topc(X31,X30))|(v2_struct_0(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.19/0.37  fof(c_0_15, plain, ![X34, X35, X36]:(((~v2_struct_0(k1_tsep_1(X34,X35,X36))|(v2_struct_0(X34)|~l1_pre_topc(X34)|v2_struct_0(X35)|~m1_pre_topc(X35,X34)|v2_struct_0(X36)|~m1_pre_topc(X36,X34)))&(v1_pre_topc(k1_tsep_1(X34,X35,X36))|(v2_struct_0(X34)|~l1_pre_topc(X34)|v2_struct_0(X35)|~m1_pre_topc(X35,X34)|v2_struct_0(X36)|~m1_pre_topc(X36,X34))))&(m1_pre_topc(k1_tsep_1(X34,X35,X36),X34)|(v2_struct_0(X34)|~l1_pre_topc(X34)|v2_struct_0(X35)|~m1_pre_topc(X35,X34)|v2_struct_0(X36)|~m1_pre_topc(X36,X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.19/0.37  fof(c_0_16, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|~v1_xboole_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.37  fof(c_0_17, plain, ![X26, X27]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26))|m1_subset_1(k1_connsp_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).
% 0.19/0.37  fof(c_0_18, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(r2_hidden(X9,X6)|r2_hidden(X9,X7))|X8!=k2_xboole_0(X6,X7))&((~r2_hidden(X10,X6)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))&(~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))))&(((~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k2_xboole_0(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.37  cnf(c_0_19, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_21, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_22, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_23, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_24, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_26, plain, (v2_struct_0(X1)|m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  fof(c_0_27, plain, ![X28, X29]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(~m1_subset_1(X29,u1_struct_0(X28))|r2_hidden(X29,k1_connsp_2(X28,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).
% 0.19/0.37  fof(c_0_28, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.37  cnf(c_0_29, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (v1_xboole_0(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))|r2_hidden(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.37  cnf(c_0_31, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_38, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X3,k1_connsp_2(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.37  cnf(c_0_39, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_connsp_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk4_0))|X1!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_41, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_42, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))|r2_hidden(esk5_0,k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35]), c_0_36]), c_0_37])).
% 0.19/0.37  cnf(c_0_44, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|X1!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (X1!=esk5_0|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))|r2_hidden(esk5_0,u1_struct_0(esk4_0))|r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~v2_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~v1_xboole_0(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_44, c_0_20])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (X1!=esk5_0|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_41])).
% 0.19/0.37  cnf(c_0_50, negated_conjecture, (v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))|r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.37  fof(c_0_51, plain, ![X22, X23]:(~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|v2_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~v2_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35]), c_0_36]), c_0_37])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.37  cnf(c_0_54, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.37  fof(c_0_55, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,X24)|l1_pre_topc(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.37  cnf(c_0_56, negated_conjecture, (v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~v2_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.19/0.37  cnf(c_0_57, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_pre_topc(k1_tsep_1(X1,X2,X3))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_54, c_0_22])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_59, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_32]), c_0_33]), c_0_34]), c_0_58])]), c_0_35]), c_0_36]), c_0_37])).
% 0.19/0.37  cnf(c_0_61, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|l1_pre_topc(k1_tsep_1(X1,X2,X3))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_59, c_0_22])).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, (v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_32]), c_0_33]), c_0_34])]), c_0_35]), c_0_36]), c_0_37])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_62]), c_0_32]), c_0_33]), c_0_34])]), c_0_37]), c_0_36]), c_0_35]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 64
% 0.19/0.37  # Proof object clause steps            : 41
% 0.19/0.37  # Proof object formula steps           : 23
% 0.19/0.37  # Proof object conjectures             : 26
% 0.19/0.37  # Proof object clause conjectures      : 23
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 22
% 0.19/0.37  # Proof object initial formulas used   : 11
% 0.19/0.37  # Proof object generating inferences   : 18
% 0.19/0.37  # Proof object simplifying inferences  : 41
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 11
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 28
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 28
% 0.19/0.37  # Processed clauses                    : 92
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 1
% 0.19/0.37  # ...remaining for further processing  : 91
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 4
% 0.19/0.37  # Backward-rewritten                   : 4
% 0.19/0.37  # Generated clauses                    : 76
% 0.19/0.37  # ...of the previous two non-trivial   : 70
% 0.19/0.37  # Contextual simplify-reflections      : 3
% 0.19/0.37  # Paramodulations                      : 66
% 0.19/0.37  # Factorizations                       : 6
% 0.19/0.37  # Equation resolutions                 : 4
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 55
% 0.19/0.37  #    Positive orientable unit clauses  : 12
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 40
% 0.19/0.37  # Current number of unprocessed clauses: 34
% 0.19/0.37  # ...number of literals in the above   : 215
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 36
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 882
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 223
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 8
% 0.19/0.37  # Unit Clause-clause subsumption calls : 75
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 2
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 4431
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.035 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.038 s
% 0.19/0.37  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
