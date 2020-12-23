%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:29 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 389 expanded)
%              Number of clauses        :   60 ( 147 expanded)
%              Number of leaves         :   13 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          :  370 (3150 expanded)
%              Number of equality atoms :   14 (  43 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t9_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( m1_connsp_2(X4,X1,X3)
                            & r1_tarski(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(t6_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( m1_connsp_2(X2,X1,X3)
               => r2_hidden(X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(c_0_13,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | ~ v3_pre_topc(X37,X36)
      | ~ r2_hidden(X38,X37)
      | m1_connsp_2(X37,X36,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_14,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( m1_connsp_2(X4,X1,X3)
                              & r1_tarski(X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_connsp_2])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ! [X45,X46] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
        | ~ v3_pre_topc(esk3_0,esk2_0) )
      & ( r2_hidden(esk4_0,esk3_0)
        | ~ v3_pre_topc(esk3_0,esk2_0) )
      & ( ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ m1_connsp_2(X45,esk2_0,esk4_0)
        | ~ r1_tarski(X45,esk3_0)
        | ~ v3_pre_topc(esk3_0,esk2_0) )
      & ( m1_subset_1(esk5_1(X46),k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ r2_hidden(X46,esk3_0)
        | ~ m1_subset_1(X46,u1_struct_0(esk2_0))
        | v3_pre_topc(esk3_0,esk2_0) )
      & ( m1_connsp_2(esk5_1(X46),esk2_0,X46)
        | ~ r2_hidden(X46,esk3_0)
        | ~ m1_subset_1(X46,u1_struct_0(esk2_0))
        | v3_pre_topc(esk3_0,esk2_0) )
      & ( r1_tarski(esk5_1(X46),esk3_0)
        | ~ r2_hidden(X46,esk3_0)
        | ~ m1_subset_1(X46,u1_struct_0(esk2_0))
        | v3_pre_topc(esk3_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_27,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_connsp_2(X1,esk2_0,esk4_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk2_0,X1)
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_32,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ r1_tarski(X24,X25)
      | r1_tarski(k1_tops_1(X23,X24),k1_tops_1(X23,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk5_1(X1),esk3_0)
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_21]),c_0_30])]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r1_tarski(X1,esk5_1(X2)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk5_1(X1),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

fof(c_0_45,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | ~ m1_subset_1(X41,u1_struct_0(X39))
      | ~ m1_connsp_2(X40,X39,X41)
      | r2_hidden(X41,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

fof(c_0_46,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_connsp_2(X35,X33,X34)
      | m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_47,plain,(
    ! [X30,X31,X32] :
      ( ( ~ m1_connsp_2(X32,X30,X31)
        | r2_hidden(X31,k1_tops_1(X30,X32))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ r2_hidden(X31,k1_tops_1(X30,X32))
        | m1_connsp_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_48,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(k1_tops_1(esk2_0,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk5_1(X1),u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_54,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | m1_subset_1(k1_tops_1(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_55,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(k1_tops_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_50])).

cnf(c_0_58,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_61,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk5_1(X1)),k1_zfmisc_1(k1_tops_1(esk2_0,esk3_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_44]),c_0_57])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_58,c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( m1_connsp_2(esk5_1(X1),esk2_0,X1)
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_66,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ v3_pre_topc(X29,X27)
        | k1_tops_1(X27,X29) = X29
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( k1_tops_1(X26,X28) != X28
        | v3_pre_topc(X28,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_68,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_23])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,esk5_1(X2)))
    | ~ r2_hidden(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,esk5_1(X1)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_22]),c_0_23])]),c_0_24]),c_0_36]),c_0_37])).

cnf(c_0_72,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_2(k1_tops_1(esk2_0,esk3_0),X1),esk3_0)
    | r1_tarski(k1_tops_1(esk2_0,esk3_0),X1)
    | ~ m1_subset_1(esk1_2(k1_tops_1(esk2_0,esk3_0),X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | k1_tops_1(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_21]),c_0_23])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)
    | ~ m1_subset_1(esk1_2(k1_tops_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk1_2(k1_tops_1(esk2_0,X1),X2),u1_struct_0(esk2_0))
    | r1_tarski(k1_tops_1(esk2_0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(esk1_2(X1,k1_tops_1(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | k1_tops_1(esk2_0,X1) != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_22]),c_0_23])])).

cnf(c_0_82,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_21])])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_68])).

cnf(c_0_85,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_81]),c_0_21])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.19/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.044 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.19/0.42  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.42  fof(t9_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 0.19/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.42  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.19/0.42  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.19/0.42  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.19/0.42  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.19/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.42  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.19/0.42  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.19/0.42  fof(c_0_13, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~m1_subset_1(X38,u1_struct_0(X36))|(~v3_pre_topc(X37,X36)|~r2_hidden(X38,X37)|m1_connsp_2(X37,X36,X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.19/0.42  fof(c_0_14, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|m1_subset_1(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.42  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2))))))))))), inference(assume_negation,[status(cth)],[t9_connsp_2])).
% 0.19/0.42  cnf(c_0_16, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_17, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  fof(c_0_18, negated_conjecture, ![X45, X46]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((m1_subset_1(esk4_0,u1_struct_0(esk2_0))|~v3_pre_topc(esk3_0,esk2_0))&((r2_hidden(esk4_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0))&(~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(esk2_0)))|(~m1_connsp_2(X45,esk2_0,esk4_0)|~r1_tarski(X45,esk3_0))|~v3_pre_topc(esk3_0,esk2_0))))&((m1_subset_1(esk5_1(X46),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X46,esk3_0)|~m1_subset_1(X46,u1_struct_0(esk2_0))|v3_pre_topc(esk3_0,esk2_0))&((m1_connsp_2(esk5_1(X46),esk2_0,X46)|~r2_hidden(X46,esk3_0)|~m1_subset_1(X46,u1_struct_0(esk2_0))|v3_pre_topc(esk3_0,esk2_0))&(r1_tarski(esk5_1(X46),esk3_0)|~r2_hidden(X46,esk3_0)|~m1_subset_1(X46,u1_struct_0(esk2_0))|v3_pre_topc(esk3_0,esk2_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.19/0.42  fof(c_0_19, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  cnf(c_0_20, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.42  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  fof(c_0_26, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.42  fof(c_0_27, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  cnf(c_0_28, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_connsp_2(X1,esk2_0,esk4_0)|~r1_tarski(X1,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_29, negated_conjecture, (m1_connsp_2(esk3_0,esk2_0,X1)|~v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.42  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_31, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  fof(c_0_32, plain, ![X23, X24, X25]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~r1_tarski(X24,X25)|r1_tarski(k1_tops_1(X23,X24),k1_tops_1(X23,X25)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.19/0.42  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_35, negated_conjecture, (r1_tarski(esk5_1(X1),esk3_0)|v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_21]), c_0_30])]), c_0_31])).
% 0.19/0.42  cnf(c_0_37, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_21])).
% 0.19/0.42  cnf(c_0_38, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,esk3_0)|~r2_hidden(X2,esk3_0)|~r1_tarski(X1,esk5_1(X2))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_35]), c_0_36]), c_0_37])).
% 0.19/0.42  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_23])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_21])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (r1_tarski(esk5_1(X1),esk3_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 0.19/0.42  fof(c_0_45, plain, ![X39, X40, X41]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(~m1_subset_1(X41,u1_struct_0(X39))|(~m1_connsp_2(X40,X39,X41)|r2_hidden(X41,X40))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.19/0.42  fof(c_0_46, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,u1_struct_0(X33))|(~m1_connsp_2(X35,X33,X34)|m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.19/0.42  fof(c_0_47, plain, ![X30, X31, X32]:((~m1_connsp_2(X32,X30,X31)|r2_hidden(X31,k1_tops_1(X30,X32))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(~r2_hidden(X31,k1_tops_1(X30,X32))|m1_connsp_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.19/0.42  fof(c_0_48, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(k1_tops_1(esk2_0,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.42  cnf(c_0_50, negated_conjecture, (r1_tarski(esk5_1(X1),u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.42  cnf(c_0_51, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.42  cnf(c_0_52, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  cnf(c_0_53, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.42  fof(c_0_54, plain, ![X21, X22]:(~l1_pre_topc(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|m1_subset_1(k1_tops_1(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.19/0.42  cnf(c_0_55, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  cnf(c_0_56, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(k1_tops_1(esk2_0,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_21])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_50])).
% 0.19/0.42  cnf(c_0_58, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.42  cnf(c_0_59, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (m1_connsp_2(esk3_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.42  cnf(c_0_61, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.42  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_55, c_0_34])).
% 0.19/0.42  cnf(c_0_63, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk5_1(X1)),k1_zfmisc_1(k1_tops_1(esk2_0,esk3_0)))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_44]), c_0_57])).
% 0.19/0.42  cnf(c_0_64, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_58, c_0_52])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (m1_connsp_2(esk5_1(X1),esk2_0,X1)|v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  fof(c_0_66, plain, ![X26, X27, X28, X29]:((~v3_pre_topc(X29,X27)|k1_tops_1(X27,X29)=X29|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X27)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(k1_tops_1(X26,X28)!=X28|v3_pre_topc(X28,X26)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X27)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.42  cnf(c_0_68, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_61, c_0_23])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))|~r2_hidden(X1,k1_tops_1(esk2_0,esk5_1(X2)))|~r2_hidden(X2,esk3_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,esk5_1(X1)))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_22]), c_0_23])]), c_0_24]), c_0_36]), c_0_37])).
% 0.19/0.42  cnf(c_0_72, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.42  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_2(k1_tops_1(esk2_0,esk3_0),X1),esk3_0)|r1_tarski(k1_tops_1(esk2_0,esk3_0),X1)|~m1_subset_1(esk1_2(k1_tops_1(esk2_0,esk3_0),X1),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,k1_tops_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_17, c_0_69])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (v3_pre_topc(X1,X2)|k1_tops_1(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_21]), c_0_23])])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)|~m1_subset_1(esk1_2(k1_tops_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk1_2(k1_tops_1(esk2_0,X1),X2),u1_struct_0(esk2_0))|r1_tarski(k1_tops_1(esk2_0,X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_75, c_0_68])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))|~r2_hidden(esk1_2(X1,k1_tops_1(esk2_0,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_76])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (v3_pre_topc(X1,esk2_0)|k1_tops_1(esk2_0,X1)!=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_22]), c_0_23])])).
% 0.19/0.42  cnf(c_0_82, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_83, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_21])])).
% 0.19/0.42  cnf(c_0_84, negated_conjecture, (r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_80, c_0_68])).
% 0.19/0.42  cnf(c_0_85, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_81]), c_0_21])])).
% 0.19/0.42  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])]), c_0_85]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 87
% 0.19/0.42  # Proof object clause steps            : 60
% 0.19/0.42  # Proof object formula steps           : 27
% 0.19/0.42  # Proof object conjectures             : 40
% 0.19/0.42  # Proof object clause conjectures      : 37
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 25
% 0.19/0.42  # Proof object initial formulas used   : 13
% 0.19/0.42  # Proof object generating inferences   : 31
% 0.19/0.42  # Proof object simplifying inferences  : 40
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 13
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 29
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 29
% 0.19/0.42  # Processed clauses                    : 317
% 0.19/0.42  # ...of these trivial                  : 2
% 0.19/0.42  # ...subsumed                          : 107
% 0.19/0.42  # ...remaining for further processing  : 208
% 0.19/0.42  # Other redundant clauses eliminated   : 2
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 5
% 0.19/0.42  # Backward-rewritten                   : 1
% 0.19/0.42  # Generated clauses                    : 501
% 0.19/0.42  # ...of the previous two non-trivial   : 455
% 0.19/0.42  # Contextual simplify-reflections      : 13
% 0.19/0.42  # Paramodulations                      : 499
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 2
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 172
% 0.19/0.42  #    Positive orientable unit clauses  : 10
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 3
% 0.19/0.42  #    Non-unit-clauses                  : 159
% 0.19/0.42  # Current number of unprocessed clauses: 172
% 0.19/0.42  # ...number of literals in the above   : 651
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 34
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 2156
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 1526
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 115
% 0.19/0.42  # Unit Clause-clause subsumption calls : 39
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 19
% 0.19/0.42  # BW rewrite match successes           : 1
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 13755
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.075 s
% 0.19/0.42  # System time              : 0.009 s
% 0.19/0.42  # Total time               : 0.084 s
% 0.19/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
