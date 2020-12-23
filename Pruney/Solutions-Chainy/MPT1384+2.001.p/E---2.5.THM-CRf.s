%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:29 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 361 expanded)
%              Number of clauses        :   45 ( 132 expanded)
%              Number of leaves         :   10 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  255 (2964 expanded)
%              Number of equality atoms :    8 (  32 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_10,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | ~ m1_subset_1(X37,u1_struct_0(X35))
      | ~ v3_pre_topc(X36,X35)
      | ~ r2_hidden(X37,X36)
      | m1_connsp_2(X36,X35,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_11,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | m1_subset_1(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,negated_conjecture,(
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

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ! [X41,X42] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( r2_hidden(esk5_0,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ m1_connsp_2(X41,esk3_0,esk5_0)
        | ~ r1_tarski(X41,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_subset_1(esk6_1(X42),k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r2_hidden(X42,esk4_0)
        | ~ m1_subset_1(X42,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_connsp_2(esk6_1(X42),esk3_0,X42)
        | ~ r2_hidden(X42,esk4_0)
        | ~ m1_subset_1(X42,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( r1_tarski(esk6_1(X42),esk4_0)
        | ~ r2_hidden(X42,esk4_0)
        | ~ m1_subset_1(X42,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_17,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ r1_tarski(X30,X31)
      | r1_tarski(k1_tops_1(X29,X30),k1_tops_1(X29,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_connsp_2(X1,esk3_0,esk5_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk4_0)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_18]),c_0_27])]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,X1),k1_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_19])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk6_1(X1),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk6_1(X1),u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,X1),k1_zfmisc_1(k1_tops_1(esk3_0,esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

fof(c_0_42,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,esk6_1(X1)),k1_zfmisc_1(k1_tops_1(esk3_0,esk4_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

fof(c_0_44,plain,(
    ! [X32,X33,X34] :
      ( ( ~ m1_connsp_2(X34,X32,X33)
        | r2_hidden(X33,k1_tops_1(X32,X34))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ r2_hidden(X33,k1_tops_1(X32,X34))
        | m1_connsp_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk6_1(X1)),k1_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_43])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( m1_connsp_2(esk6_1(X1),esk3_0,X1)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_49,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | r1_tarski(k1_tops_1(X27,X28),X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk6_1(X2)))
    | ~ r2_hidden(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,esk6_1(X1)))
    | ~ m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_19]),c_0_20])]),c_0_21]),c_0_32]),c_0_33])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_41])).

fof(c_0_55,plain,(
    ! [X25,X26] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | v3_pre_topc(k1_tops_1(X25,X26),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_18]),c_0_19])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(esk1_2(X1,k1_tops_1(esk3_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_60,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk3_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_20]),c_0_19])])).

cnf(c_0_64,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_18])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.21/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.029 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.21/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.39  fof(t9_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 0.21/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.39  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.21/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.39  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.21/0.39  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.21/0.39  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.21/0.39  fof(c_0_10, plain, ![X35, X36, X37]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(~m1_subset_1(X37,u1_struct_0(X35))|(~v3_pre_topc(X36,X35)|~r2_hidden(X37,X36)|m1_connsp_2(X36,X35,X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.21/0.39  fof(c_0_11, plain, ![X22, X23, X24]:(~r2_hidden(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(X24))|m1_subset_1(X22,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.39  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2))))))))))), inference(assume_negation,[status(cth)],[t9_connsp_2])).
% 0.21/0.39  cnf(c_0_13, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_14, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  fof(c_0_15, negated_conjecture, ![X41, X42]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((m1_subset_1(esk5_0,u1_struct_0(esk3_0))|~v3_pre_topc(esk4_0,esk3_0))&((r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0))&(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~m1_connsp_2(X41,esk3_0,esk5_0)|~r1_tarski(X41,esk4_0))|~v3_pre_topc(esk4_0,esk3_0))))&((m1_subset_1(esk6_1(X42),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X42,esk4_0)|~m1_subset_1(X42,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))&((m1_connsp_2(esk6_1(X42),esk3_0,X42)|~r2_hidden(X42,esk4_0)|~m1_subset_1(X42,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))&(r1_tarski(esk6_1(X42),esk4_0)|~r2_hidden(X42,esk4_0)|~m1_subset_1(X42,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.21/0.39  fof(c_0_16, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.39  cnf(c_0_17, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  fof(c_0_23, plain, ![X29, X30, X31]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(~r1_tarski(X30,X31)|r1_tarski(k1_tops_1(X29,X30),k1_tops_1(X29,X31)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.21/0.39  fof(c_0_24, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_connsp_2(X1,esk3_0,esk5_0)|~r1_tarski(X1,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.21/0.39  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_29, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (r1_tarski(esk6_1(X1),esk4_0)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_18]), c_0_27])]), c_0_28])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 0.21/0.39  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,X1),k1_tops_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_18]), c_0_19])])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk6_1(X1),k1_zfmisc_1(esk4_0))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (r1_tarski(esk6_1(X1),u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_32]), c_0_33])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,X1),k1_zfmisc_1(k1_tops_1(esk3_0,esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (r1_tarski(esk6_1(X1),esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_37])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_38])).
% 0.21/0.39  fof(c_0_42, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,esk6_1(X1)),k1_zfmisc_1(k1_tops_1(esk3_0,esk4_0)))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.21/0.39  fof(c_0_44, plain, ![X32, X33, X34]:((~m1_connsp_2(X34,X32,X33)|r2_hidden(X33,k1_tops_1(X32,X34))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~r2_hidden(X33,k1_tops_1(X32,X34))|m1_connsp_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.21/0.39  cnf(c_0_45, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk6_1(X1)),k1_tops_1(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_43])).
% 0.21/0.39  cnf(c_0_47, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (m1_connsp_2(esk6_1(X1),esk3_0,X1)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  fof(c_0_49, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|r1_tarski(k1_tops_1(X27,X28),X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))|~r2_hidden(X1,k1_tops_1(esk3_0,esk6_1(X2)))|~r2_hidden(X2,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,esk6_1(X1)))|~m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_19]), c_0_20])]), c_0_21]), c_0_32]), c_0_33])).
% 0.21/0.39  cnf(c_0_52, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.39  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_41])).
% 0.21/0.39  fof(c_0_55, plain, ![X25, X26]:(~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|v3_pre_topc(k1_tops_1(X25,X26),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.21/0.39  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_18]), c_0_19])])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~r2_hidden(esk1_2(X1,k1_tops_1(esk3_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.39  cnf(c_0_59, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_60, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.39  cnf(c_0_61, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.39  cnf(c_0_62, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (v3_pre_topc(k1_tops_1(esk3_0,X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_20]), c_0_19])])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_18])]), c_0_32]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 66
% 0.21/0.39  # Proof object clause steps            : 45
% 0.21/0.39  # Proof object formula steps           : 21
% 0.21/0.39  # Proof object conjectures             : 33
% 0.21/0.39  # Proof object clause conjectures      : 30
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 22
% 0.21/0.39  # Proof object initial formulas used   : 10
% 0.21/0.39  # Proof object generating inferences   : 20
% 0.21/0.39  # Proof object simplifying inferences  : 33
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 11
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 29
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 29
% 0.21/0.39  # Processed clauses                    : 260
% 0.21/0.39  # ...of these trivial                  : 2
% 0.21/0.39  # ...subsumed                          : 61
% 0.21/0.39  # ...remaining for further processing  : 197
% 0.21/0.39  # Other redundant clauses eliminated   : 4
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 3
% 0.21/0.39  # Backward-rewritten                   : 46
% 0.21/0.39  # Generated clauses                    : 386
% 0.21/0.39  # ...of the previous two non-trivial   : 385
% 0.21/0.39  # Contextual simplify-reflections      : 17
% 0.21/0.39  # Paramodulations                      : 380
% 0.21/0.39  # Factorizations                       : 2
% 0.21/0.39  # Equation resolutions                 : 4
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 116
% 0.21/0.39  #    Positive orientable unit clauses  : 13
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 2
% 0.21/0.39  #    Non-unit-clauses                  : 101
% 0.21/0.39  # Current number of unprocessed clauses: 146
% 0.21/0.39  # ...number of literals in the above   : 480
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 77
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 2166
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 1712
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 66
% 0.21/0.39  # Unit Clause-clause subsumption calls : 73
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 24
% 0.21/0.39  # BW rewrite match successes           : 2
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 10311
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.042 s
% 0.21/0.39  # System time              : 0.008 s
% 0.21/0.39  # Total time               : 0.050 s
% 0.21/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
