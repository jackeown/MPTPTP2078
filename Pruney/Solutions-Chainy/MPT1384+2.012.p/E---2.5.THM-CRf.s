%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:31 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 546 expanded)
%              Number of clauses        :   62 ( 209 expanded)
%              Number of leaves         :   12 ( 134 expanded)
%              Depth                    :   15
%              Number of atoms          :  440 (4418 expanded)
%              Number of equality atoms :   13 (  47 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t54_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,k1_tops_1(X1,X3))
          <=> ? [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                & v3_pre_topc(X4,X1)
                & r1_tarski(X4,X3)
                & r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

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

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ r2_hidden(X9,X8)
      | r2_hidden(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | r1_tarski(k1_tops_1(X19,X20),X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_20,plain,(
    ! [X21,X22,X23] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ r1_tarski(X22,X23)
      | r1_tarski(k1_tops_1(X21,X22),k1_tops_1(X21,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_21,negated_conjecture,(
    ! [X42,X43] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( r2_hidden(esk5_0,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ m1_connsp_2(X42,esk3_0,esk5_0)
        | ~ r1_tarski(X42,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_subset_1(esk6_1(X43),k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r2_hidden(X43,esk4_0)
        | ~ m1_subset_1(X43,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_connsp_2(esk6_1(X43),esk3_0,X43)
        | ~ r2_hidden(X43,esk4_0)
        | ~ m1_subset_1(X43,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( r1_tarski(esk6_1(X43),esk4_0)
        | ~ r2_hidden(X43,esk4_0)
        | ~ m1_subset_1(X43,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X33,X34,X35] :
      ( ( ~ m1_connsp_2(X35,X33,X34)
        | r2_hidden(X34,k1_tops_1(X33,X35))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r2_hidden(X34,k1_tops_1(X33,X35))
        | m1_connsp_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_28,plain,(
    ! [X24,X25,X26,X28] :
      ( ( m1_subset_1(esk2_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))
        | ~ r2_hidden(X25,k1_tops_1(X24,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( v3_pre_topc(esk2_3(X24,X25,X26),X24)
        | ~ r2_hidden(X25,k1_tops_1(X24,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r1_tarski(esk2_3(X24,X25,X26),X26)
        | ~ r2_hidden(X25,k1_tops_1(X24,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(X25,esk2_3(X24,X25,X26))
        | ~ r2_hidden(X25,k1_tops_1(X24,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_pre_topc(X28,X24)
        | ~ r1_tarski(X28,X26)
        | ~ r2_hidden(X25,X28)
        | r2_hidden(X25,k1_tops_1(X24,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_connsp_2(X1,esk3_0,esk5_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ r2_hidden(X1,k1_tops_1(X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_40,plain,(
    ! [X10,X11,X12] :
      ( ( m1_subset_1(esk1_3(X10,X11,X12),X10)
        | r1_tarski(X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r1_tarski(X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | r1_tarski(X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_connsp_2(X1,esk3_0,esk5_0)
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,esk2_3(X2,X3,X4))
    | ~ r2_hidden(X3,k1_tops_1(X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_41])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X4,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_58,plain,
    ( m1_connsp_2(X1,X2,esk1_3(X3,k1_tops_1(X2,X1),X4))
    | v2_struct_0(X2)
    | r1_tarski(k1_tops_1(X2,X1),X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk1_3(X3,k1_tops_1(X2,X1),X4),u1_struct_0(X2))
    | ~ m1_subset_1(k1_tops_1(X2,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ m1_connsp_2(esk6_1(X3),esk3_0,X1)
    | ~ r2_hidden(X3,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(esk6_1(X3),X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_33]),c_0_34])]),c_0_35]),c_0_55]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( m1_connsp_2(esk6_1(X1),esk3_0,X1)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_3(X1,k1_tops_1(esk3_0,esk4_0),X2),esk4_0)
    | r1_tarski(k1_tops_1(esk3_0,esk4_0),X2)
    | ~ m1_subset_1(esk1_3(X1,k1_tops_1(esk3_0,esk4_0),X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_33]),c_0_34]),c_0_32])]),c_0_35])).

cnf(c_0_63,plain,
    ( m1_subset_1(esk1_3(X1,k1_tops_1(X2,X3),X4),u1_struct_0(X2))
    | r1_tarski(k1_tops_1(X2,X3),X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k1_tops_1(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk6_1(X1),X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_55]),c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk4_0)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_66,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk1_3(X1,k1_tops_1(esk3_0,esk4_0),X2),esk4_0)
    | r1_tarski(k1_tops_1(esk3_0,esk4_0),X2)
    | ~ m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_33]),c_0_34]),c_0_32])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk6_1(X1),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_64]),c_0_34])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_56]),c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

fof(c_0_71,plain,(
    ! [X29,X30,X31,X32] :
      ( ( ~ v3_pre_topc(X32,X30)
        | k1_tops_1(X30,X32) = X32
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ l1_pre_topc(X30)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( k1_tops_1(X29,X31) != X31
        | v3_pre_topc(X31,X29)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ l1_pre_topc(X30)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk4_0,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_32]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_tops_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_18])).

cnf(c_0_74,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,X2))
    | ~ r2_hidden(esk1_3(X3,X1,k1_tops_1(esk3_0,X2)),esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk3_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_tops_1(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_46])).

cnf(c_0_77,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | k1_tops_1(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_32]),c_0_34])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk3_0,X1))
    | ~ m1_subset_1(k1_tops_1(esk3_0,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X2))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_50])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)
    | ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_18])).

cnf(c_0_81,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) != esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_32]),c_0_33]),c_0_34])]),c_0_55])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk3_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X2))
    | ~ r1_tarski(k1_tops_1(esk3_0,X1),X2)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_18])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_26]),c_0_34]),c_0_32])])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_32]),c_0_46])]),c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_18]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.81  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.60/0.81  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.60/0.81  #
% 0.60/0.81  # Preprocessing time       : 0.028 s
% 0.60/0.81  
% 0.60/0.81  # Proof found!
% 0.60/0.81  # SZS status Theorem
% 0.60/0.81  # SZS output start CNFRefutation
% 0.60/0.81  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.60/0.81  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.60/0.81  fof(t9_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 0.60/0.81  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.60/0.81  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.60/0.81  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.60/0.81  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.60/0.81  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.60/0.81  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.60/0.81  fof(t54_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 0.60/0.81  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.60/0.81  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.60/0.81  fof(c_0_12, plain, ![X7, X8, X9]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|(~r2_hidden(X9,X8)|r2_hidden(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.60/0.81  fof(c_0_13, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.60/0.81  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2))))))))))), inference(assume_negation,[status(cth)],[t9_connsp_2])).
% 0.60/0.81  fof(c_0_15, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~m1_subset_1(X38,u1_struct_0(X36))|(~v3_pre_topc(X37,X36)|~r2_hidden(X38,X37)|m1_connsp_2(X37,X36,X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.60/0.81  fof(c_0_16, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.60/0.81  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.60/0.81  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.81  fof(c_0_19, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|r1_tarski(k1_tops_1(X19,X20),X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.60/0.81  fof(c_0_20, plain, ![X21, X22, X23]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~r1_tarski(X22,X23)|r1_tarski(k1_tops_1(X21,X22),k1_tops_1(X21,X23)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.60/0.81  fof(c_0_21, negated_conjecture, ![X42, X43]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((m1_subset_1(esk5_0,u1_struct_0(esk3_0))|~v3_pre_topc(esk4_0,esk3_0))&((r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0))&(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~m1_connsp_2(X42,esk3_0,esk5_0)|~r1_tarski(X42,esk4_0))|~v3_pre_topc(esk4_0,esk3_0))))&((m1_subset_1(esk6_1(X43),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X43,esk4_0)|~m1_subset_1(X43,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))&((m1_connsp_2(esk6_1(X43),esk3_0,X43)|~r2_hidden(X43,esk4_0)|~m1_subset_1(X43,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))&(r1_tarski(esk6_1(X43),esk4_0)|~r2_hidden(X43,esk4_0)|~m1_subset_1(X43,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).
% 0.60/0.81  cnf(c_0_22, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.60/0.81  cnf(c_0_23, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.60/0.81  fof(c_0_24, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.60/0.81  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.60/0.81  cnf(c_0_26, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.81  fof(c_0_27, plain, ![X33, X34, X35]:((~m1_connsp_2(X35,X33,X34)|r2_hidden(X34,k1_tops_1(X33,X35))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~r2_hidden(X34,k1_tops_1(X33,X35))|m1_connsp_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.60/0.81  fof(c_0_28, plain, ![X24, X25, X26, X28]:(((((m1_subset_1(esk2_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))|~r2_hidden(X25,k1_tops_1(X24,X26))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(v3_pre_topc(esk2_3(X24,X25,X26),X24)|~r2_hidden(X25,k1_tops_1(X24,X26))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24))))&(r1_tarski(esk2_3(X24,X25,X26),X26)|~r2_hidden(X25,k1_tops_1(X24,X26))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24))))&(r2_hidden(X25,esk2_3(X24,X25,X26))|~r2_hidden(X25,k1_tops_1(X24,X26))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24))))&(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X24)))|~v3_pre_topc(X28,X24)|~r1_tarski(X28,X26)|~r2_hidden(X25,X28)|r2_hidden(X25,k1_tops_1(X24,X26))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).
% 0.60/0.81  cnf(c_0_29, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.60/0.81  cnf(c_0_30, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_connsp_2(X1,esk3_0,esk5_0)|~r1_tarski(X1,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_31, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_22, c_0_23])).
% 0.60/0.81  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.81  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.81  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~l1_pre_topc(X3)|~r2_hidden(X1,k1_tops_1(X3,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.60/0.81  cnf(c_0_39, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.60/0.81  fof(c_0_40, plain, ![X10, X11, X12]:((m1_subset_1(esk1_3(X10,X11,X12),X10)|r1_tarski(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X10))|~m1_subset_1(X11,k1_zfmisc_1(X10)))&((r2_hidden(esk1_3(X10,X11,X12),X11)|r1_tarski(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X10))|~m1_subset_1(X11,k1_zfmisc_1(X10)))&(~r2_hidden(esk1_3(X10,X11,X12),X12)|r1_tarski(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X10))|~m1_subset_1(X11,k1_zfmisc_1(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.60/0.81  cnf(c_0_41, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.60/0.81  cnf(c_0_42, plain, (r2_hidden(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~r2_hidden(X1,k1_tops_1(X2,X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_25, c_0_29])).
% 0.60/0.81  cnf(c_0_43, negated_conjecture, (~m1_connsp_2(X1,esk3_0,esk5_0)|~v3_pre_topc(esk4_0,esk3_0)|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_18])).
% 0.60/0.81  cnf(c_0_44, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.60/0.81  cnf(c_0_45, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.60/0.81  cnf(c_0_46, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 0.60/0.81  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_48, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.60/0.81  cnf(c_0_49, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.60/0.81  cnf(c_0_50, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.60/0.81  cnf(c_0_51, plain, (m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X1,esk2_3(X2,X3,X4))|~r2_hidden(X3,k1_tops_1(X2,X4))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_23, c_0_41])).
% 0.60/0.81  cnf(c_0_52, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.60/0.81  cnf(c_0_53, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X4,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_42, c_0_39])).
% 0.60/0.81  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_55, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.60/0.81  cnf(c_0_56, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_32])).
% 0.60/0.81  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_connsp_2(esk4_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.60/0.81  cnf(c_0_58, plain, (m1_connsp_2(X1,X2,esk1_3(X3,k1_tops_1(X2,X1),X4))|v2_struct_0(X2)|r1_tarski(k1_tops_1(X2,X1),X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(esk1_3(X3,k1_tops_1(X2,X1),X4),u1_struct_0(X2))|~m1_subset_1(k1_tops_1(X2,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.60/0.81  cnf(c_0_59, plain, (m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.60/0.81  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~m1_connsp_2(esk6_1(X3),esk3_0,X1)|~r2_hidden(X3,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r1_tarski(esk6_1(X3),X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_33]), c_0_34])]), c_0_35]), c_0_55]), c_0_56])).
% 0.60/0.81  cnf(c_0_61, negated_conjecture, (m1_connsp_2(esk6_1(X1),esk3_0,X1)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_3(X1,k1_tops_1(esk3_0,esk4_0),X2),esk4_0)|r1_tarski(k1_tops_1(esk3_0,esk4_0),X2)|~m1_subset_1(esk1_3(X1,k1_tops_1(esk3_0,esk4_0),X2),u1_struct_0(esk3_0))|~m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_33]), c_0_34]), c_0_32])]), c_0_35])).
% 0.60/0.81  cnf(c_0_63, plain, (m1_subset_1(esk1_3(X1,k1_tops_1(X2,X3),X4),u1_struct_0(X2))|r1_tarski(k1_tops_1(X2,X3),X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(k1_tops_1(X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_50])).
% 0.60/0.81  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~r2_hidden(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk6_1(X1),X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_55]), c_0_56])).
% 0.60/0.81  cnf(c_0_65, negated_conjecture, (r1_tarski(esk6_1(X1),esk4_0)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_66, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.60/0.81  cnf(c_0_67, negated_conjecture, (r2_hidden(esk1_3(X1,k1_tops_1(esk3_0,esk4_0),X2),esk4_0)|r1_tarski(k1_tops_1(esk3_0,esk4_0),X2)|~m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_33]), c_0_34]), c_0_32])])).
% 0.60/0.81  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~r2_hidden(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk6_1(X1),X3)|~r1_tarski(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_64]), c_0_34])])).
% 0.60/0.81  cnf(c_0_69, negated_conjecture, (r1_tarski(esk6_1(X1),esk4_0)|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_56]), c_0_55])).
% 0.60/0.81  cnf(c_0_70, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)|~m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(X1))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.60/0.81  fof(c_0_71, plain, ![X29, X30, X31, X32]:((~v3_pre_topc(X32,X30)|k1_tops_1(X30,X32)=X32|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|~l1_pre_topc(X30)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(k1_tops_1(X29,X31)!=X31|v3_pre_topc(X31,X29)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|~l1_pre_topc(X30)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.60/0.81  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~r2_hidden(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk4_0,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_32]), c_0_69])).
% 0.60/0.81  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_70, c_0_18])).
% 0.60/0.81  cnf(c_0_74, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.60/0.81  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,X2))|~r2_hidden(esk1_3(X3,X1,k1_tops_1(esk3_0,X2)),esk4_0)|~m1_subset_1(k1_tops_1(esk3_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_66, c_0_72])).
% 0.60/0.81  cnf(c_0_76, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_tops_1(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_73, c_0_46])).
% 0.60/0.81  cnf(c_0_77, negated_conjecture, (v3_pre_topc(X1,X2)|k1_tops_1(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_32]), c_0_34])])).
% 0.60/0.81  cnf(c_0_78, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk3_0,X1))|~m1_subset_1(k1_tops_1(esk3_0,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(X2))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_50])).
% 0.60/0.81  cnf(c_0_79, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.81  cnf(c_0_80, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)|~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_18])).
% 0.60/0.81  cnf(c_0_81, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)!=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_32]), c_0_33]), c_0_34])]), c_0_55])).
% 0.60/0.81  cnf(c_0_82, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk3_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(X2))|~r1_tarski(k1_tops_1(esk3_0,X1),X2)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_78, c_0_18])).
% 0.60/0.81  cnf(c_0_83, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_26]), c_0_34]), c_0_32])])).
% 0.60/0.81  cnf(c_0_84, negated_conjecture, (~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.60/0.81  cnf(c_0_85, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_32]), c_0_46])]), c_0_84])).
% 0.60/0.81  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_18]), c_0_46])]), ['proof']).
% 0.60/0.81  # SZS output end CNFRefutation
% 0.60/0.81  # Proof object total steps             : 87
% 0.60/0.81  # Proof object clause steps            : 62
% 0.60/0.81  # Proof object formula steps           : 25
% 0.60/0.81  # Proof object conjectures             : 38
% 0.60/0.81  # Proof object clause conjectures      : 35
% 0.60/0.81  # Proof object formula conjectures     : 3
% 0.60/0.81  # Proof object initial clauses used    : 25
% 0.60/0.81  # Proof object initial formulas used   : 12
% 0.60/0.81  # Proof object generating inferences   : 35
% 0.60/0.81  # Proof object simplifying inferences  : 51
% 0.60/0.81  # Training examples: 0 positive, 0 negative
% 0.60/0.81  # Parsed axioms                        : 12
% 0.60/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.81  # Initial clauses                      : 32
% 0.60/0.81  # Removed in clause preprocessing      : 0
% 0.60/0.81  # Initial clauses in saturation        : 32
% 0.60/0.81  # Processed clauses                    : 3693
% 0.60/0.81  # ...of these trivial                  : 36
% 0.60/0.81  # ...subsumed                          : 2599
% 0.60/0.81  # ...remaining for further processing  : 1058
% 0.60/0.81  # Other redundant clauses eliminated   : 2
% 0.60/0.81  # Clauses deleted for lack of memory   : 0
% 0.60/0.81  # Backward-subsumed                    : 242
% 0.60/0.81  # Backward-rewritten                   : 0
% 0.60/0.81  # Generated clauses                    : 10098
% 0.60/0.81  # ...of the previous two non-trivial   : 9486
% 0.60/0.81  # Contextual simplify-reflections      : 227
% 0.60/0.81  # Paramodulations                      : 10096
% 0.60/0.81  # Factorizations                       : 0
% 0.60/0.81  # Equation resolutions                 : 2
% 0.60/0.81  # Propositional unsat checks           : 0
% 0.60/0.81  #    Propositional check models        : 0
% 0.60/0.81  #    Propositional check unsatisfiable : 0
% 0.60/0.81  #    Propositional clauses             : 0
% 0.60/0.81  #    Propositional clauses after purity: 0
% 0.60/0.81  #    Propositional unsat core size     : 0
% 0.60/0.81  #    Propositional preprocessing time  : 0.000
% 0.60/0.81  #    Propositional encoding time       : 0.000
% 0.60/0.81  #    Propositional solver time         : 0.000
% 0.60/0.81  #    Success case prop preproc time    : 0.000
% 0.60/0.81  #    Success case prop encoding time   : 0.000
% 0.60/0.81  #    Success case prop solver time     : 0.000
% 0.60/0.81  # Current number of processed clauses  : 814
% 0.60/0.81  #    Positive orientable unit clauses  : 5
% 0.60/0.81  #    Positive unorientable unit clauses: 0
% 0.60/0.81  #    Negative unit clauses             : 7
% 0.60/0.81  #    Non-unit-clauses                  : 802
% 0.60/0.81  # Current number of unprocessed clauses: 5662
% 0.60/0.81  # ...number of literals in the above   : 56510
% 0.60/0.81  # Current number of archived formulas  : 0
% 0.60/0.81  # Current number of archived clauses   : 242
% 0.60/0.81  # Clause-clause subsumption calls (NU) : 223303
% 0.60/0.81  # Rec. Clause-clause subsumption calls : 20745
% 0.60/0.81  # Non-unit clause-clause subsumptions  : 2207
% 0.60/0.81  # Unit Clause-clause subsumption calls : 1037
% 0.60/0.81  # Rewrite failures with RHS unbound    : 0
% 0.60/0.81  # BW rewrite match attempts            : 9
% 0.60/0.81  # BW rewrite match successes           : 0
% 0.60/0.81  # Condensation attempts                : 0
% 0.60/0.81  # Condensation successes               : 0
% 0.60/0.81  # Termbank termtop insertions          : 374389
% 0.60/0.81  
% 0.60/0.81  # -------------------------------------------------
% 0.60/0.81  # User time                : 0.454 s
% 0.60/0.81  # System time              : 0.008 s
% 0.60/0.81  # Total time               : 0.462 s
% 0.60/0.81  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
