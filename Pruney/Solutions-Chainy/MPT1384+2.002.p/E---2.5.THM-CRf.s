%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:29 EST 2020

% Result     : Theorem 0.80s
% Output     : CNFRefutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 781 expanded)
%              Number of clauses        :   74 ( 301 expanded)
%              Number of leaves         :   13 ( 193 expanded)
%              Depth                    :   17
%              Number of atoms          :  485 (6164 expanded)
%              Number of equality atoms :   13 (  49 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(t8_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & r1_tarski(X4,X3)
                    & r2_hidden(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_15,negated_conjecture,(
    ! [X45,X46] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( r2_hidden(esk5_0,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ m1_connsp_2(X45,esk3_0,esk5_0)
        | ~ r1_tarski(X45,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_subset_1(esk6_1(X46),k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r2_hidden(X46,esk4_0)
        | ~ m1_subset_1(X46,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_connsp_2(esk6_1(X46),esk3_0,X46)
        | ~ r2_hidden(X46,esk4_0)
        | ~ m1_subset_1(X46,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( r1_tarski(esk6_1(X46),esk4_0)
        | ~ r2_hidden(X46,esk4_0)
        | ~ m1_subset_1(X46,u1_struct_0(esk3_0))
        | v3_pre_topc(esk4_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).

fof(c_0_16,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | ~ v3_pre_topc(X35,X34)
      | ~ r2_hidden(X36,X35)
      | m1_connsp_2(X35,X34,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,plain,(
    ! [X37,X38,X39,X41] :
      ( ( m1_subset_1(esk2_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_connsp_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( v3_pre_topc(esk2_3(X37,X38,X39),X37)
        | ~ m1_connsp_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r1_tarski(esk2_3(X37,X38,X39),X39)
        | ~ m1_connsp_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(X38,esk2_3(X37,X38,X39))
        | ~ m1_connsp_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ v3_pre_topc(X41,X37)
        | ~ r1_tarski(X41,X39)
        | ~ r2_hidden(X38,X41)
        | m1_connsp_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).

fof(c_0_19,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | r1_tarski(k1_tops_1(X22,X23),X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( m1_connsp_2(X3,X2,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_connsp_2(X1,esk3_0,esk5_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X4,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X4)
    | ~ r1_tarski(X4,X1) ),
    inference(csr,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X1,k1_tops_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_connsp_2(X1,esk3_0,esk5_0)
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_21]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_46,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_connsp_2(X33,X31,X32)
      | m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_47,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ v3_pre_topc(X2,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_2(X1,u1_struct_0(esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(k1_tops_1(X1,X2),X3),X2)
    | r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk4_0)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28]),c_0_44])]),c_0_45])).

cnf(c_0_53,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ v3_pre_topc(X2,esk3_0)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,u1_struct_0(esk3_0))
    | ~ r1_tarski(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_tops_1(X1,esk4_0),u1_struct_0(esk3_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_57,plain,(
    ! [X20,X21] :
      ( ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | v3_pre_topc(k1_tops_1(X20,X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_58,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(k1_tops_1(X18,X19),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk6_1(X1),esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | r1_tarski(esk2_3(X1,X2,X3),X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ v3_pre_topc(k1_tops_1(X2,esk4_0),esk3_0)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,k1_tops_1(X2,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_29])).

cnf(c_0_63,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_65,plain,(
    ! [X28,X29,X30] :
      ( ( ~ m1_connsp_2(X30,X28,X29)
        | r2_hidden(X29,k1_tops_1(X28,X30))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ r2_hidden(X29,k1_tops_1(X28,X30))
        | m1_connsp_2(X30,X28,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk6_1(esk1_2(esk4_0,X1)),esk4_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_41])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X2,esk2_3(X1,X4,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_60])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,esk2_3(X1,X2,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_61,c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_34]),c_0_21]),c_0_33])])).

cnf(c_0_70,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ v3_pre_topc(k1_tops_1(esk3_0,X2),esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ r1_tarski(k1_tops_1(esk3_0,X2),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_64]),c_0_34])])).

cnf(c_0_71,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | r1_tarski(esk4_0,X2)
    | ~ r2_hidden(X1,esk6_1(esk1_2(esk4_0,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_66])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,esk1_2(k1_tops_1(esk3_0,esk4_0),X1))
    | r1_tarski(k1_tops_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_41])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ r1_tarski(k1_tops_1(esk3_0,X2),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_63]),c_0_33]),c_0_34])])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_71,c_0_54])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk1_2(k1_tops_1(X1,esk6_1(esk1_2(esk4_0,X2))),X3),esk4_0)
    | r1_tarski(k1_tops_1(X1,esk6_1(esk1_2(esk4_0,X2))),X3)
    | r1_tarski(esk4_0,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk6_1(esk1_2(esk4_0,X2)),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_49])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk1_2(k1_tops_1(esk3_0,esk4_0),X1),esk4_0)
    | r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(esk1_2(k1_tops_1(esk3_0,esk4_0),X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_80,plain,
    ( m1_subset_1(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_41])).

fof(c_0_81,plain,(
    ! [X24,X25,X26,X27] :
      ( ( ~ v3_pre_topc(X27,X25)
        | k1_tops_1(X25,X27) = X27
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X25)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( k1_tops_1(X24,X26) != X26
        | v3_pre_topc(X26,X24)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X25)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_82,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | ~ m1_connsp_2(X2,esk3_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(k1_tops_1(esk3_0,X2),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k1_tops_1(X1,esk6_1(esk1_2(esk4_0,X2))),esk4_0)
    | r1_tarski(esk4_0,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk6_1(esk1_2(esk4_0,X2)),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( m1_connsp_2(esk6_1(X1),esk3_0,X1)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk1_2(k1_tops_1(esk3_0,esk4_0),X1),esk4_0)
    | r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)
    | ~ r1_tarski(k1_tops_1(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | r1_tarski(esk4_0,X2)
    | ~ m1_connsp_2(esk6_1(esk1_2(esk4_0,X2)),esk3_0,X1)
    | ~ m1_subset_1(esk6_1(esk1_2(esk4_0,X2)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_34])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_84]),c_0_33]),c_0_34])]),c_0_35]),c_0_52]),c_0_51])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)
    | ~ r1_tarski(k1_tops_1(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_85])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_tops_1(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_64])).

cnf(c_0_91,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | k1_tops_1(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_21]),c_0_34])])).

cnf(c_0_92,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,X1)
    | r1_tarski(esk4_0,X2)
    | ~ m1_connsp_2(esk6_1(esk1_2(esk4_0,X2)),esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_41])).

cnf(c_0_93,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_34]),c_0_21])])).

cnf(c_0_95,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) != esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_21]),c_0_33]),c_0_34])]),c_0_52])).

cnf(c_0_96,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,esk1_2(X2,k1_tops_1(X1,X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk1_2(X2,k1_tops_1(X1,X3)),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_77])).

cnf(c_0_97,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk3_0,esk1_2(esk4_0,X1))
    | r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_84]),c_0_52]),c_0_41])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( ~ m1_subset_1(esk1_2(esk4_0,k1_tops_1(esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_33]),c_0_34])]),c_0_35]),c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_80]),c_0_28])]),c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:17:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.80/1.01  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.80/1.01  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.80/1.01  #
% 0.80/1.01  # Preprocessing time       : 0.030 s
% 0.80/1.01  
% 0.80/1.01  # Proof found!
% 0.80/1.01  # SZS status Theorem
% 0.80/1.01  # SZS output start CNFRefutation
% 0.80/1.01  fof(t9_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 0.80/1.01  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.80/1.01  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.80/1.01  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.80/1.01  fof(t8_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 0.80/1.01  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.80/1.01  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.80/1.01  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.80/1.01  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.80/1.01  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.80/1.01  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.80/1.01  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.80/1.01  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 0.80/1.01  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2))))))))))), inference(assume_negation,[status(cth)],[t9_connsp_2])).
% 0.80/1.01  fof(c_0_14, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.80/1.01  fof(c_0_15, negated_conjecture, ![X45, X46]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((m1_subset_1(esk5_0,u1_struct_0(esk3_0))|~v3_pre_topc(esk4_0,esk3_0))&((r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0))&(~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~m1_connsp_2(X45,esk3_0,esk5_0)|~r1_tarski(X45,esk4_0))|~v3_pre_topc(esk4_0,esk3_0))))&((m1_subset_1(esk6_1(X46),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X46,esk4_0)|~m1_subset_1(X46,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))&((m1_connsp_2(esk6_1(X46),esk3_0,X46)|~r2_hidden(X46,esk4_0)|~m1_subset_1(X46,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))&(r1_tarski(esk6_1(X46),esk4_0)|~r2_hidden(X46,esk4_0)|~m1_subset_1(X46,u1_struct_0(esk3_0))|v3_pre_topc(esk4_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).
% 0.80/1.01  fof(c_0_16, plain, ![X34, X35, X36]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|(~m1_subset_1(X36,u1_struct_0(X34))|(~v3_pre_topc(X35,X34)|~r2_hidden(X36,X35)|m1_connsp_2(X35,X34,X36))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.80/1.01  fof(c_0_17, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.80/1.01  fof(c_0_18, plain, ![X37, X38, X39, X41]:(((((m1_subset_1(esk2_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X37)))|~m1_connsp_2(X39,X37,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(v3_pre_topc(esk2_3(X37,X38,X39),X37)|~m1_connsp_2(X39,X37,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37))))&(r1_tarski(esk2_3(X37,X38,X39),X39)|~m1_connsp_2(X39,X37,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37))))&(r2_hidden(X38,esk2_3(X37,X38,X39))|~m1_connsp_2(X39,X37,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37))))&(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X37)))|~v3_pre_topc(X41,X37)|~r1_tarski(X41,X39)|~r2_hidden(X38,X41)|m1_connsp_2(X39,X37,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).
% 0.80/1.01  fof(c_0_19, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.80/1.01  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.80/1.01  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.80/1.01  fof(c_0_22, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|r1_tarski(k1_tops_1(X22,X23),X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.80/1.01  cnf(c_0_23, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.80/1.01  cnf(c_0_24, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.80/1.01  fof(c_0_25, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.80/1.01  cnf(c_0_26, plain, (m1_connsp_2(X3,X2,X4)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.80/1.01  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.80/1.01  cnf(c_0_28, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.80/1.01  cnf(c_0_29, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.80/1.01  cnf(c_0_30, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_connsp_2(X1,esk3_0,esk5_0)|~r1_tarski(X1,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.80/1.01  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.80/1.01  cnf(c_0_32, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.80/1.01  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.80/1.01  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.80/1.01  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.80/1.01  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.80/1.01  cnf(c_0_37, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X4,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X4)|~r1_tarski(X4,X1)), inference(csr,[status(thm)],[c_0_26, c_0_24])).
% 0.80/1.01  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.80/1.01  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.80/1.01  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r2_hidden(X1,k1_tops_1(X3,X2))), inference(spm,[status(thm)],[c_0_27, c_0_29])).
% 0.80/1.01  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.80/1.01  cnf(c_0_42, negated_conjecture, (~m1_connsp_2(X1,esk3_0,esk5_0)|~v3_pre_topc(esk4_0,esk3_0)|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.80/1.01  cnf(c_0_43, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_21]), c_0_33]), c_0_34])]), c_0_35])).
% 0.80/1.01  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.80/1.01  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.80/1.01  fof(c_0_46, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~m1_connsp_2(X33,X31,X32)|m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.80/1.01  cnf(c_0_47, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~v3_pre_topc(X2,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,X2)|~r1_tarski(X2,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_33]), c_0_34])]), c_0_35])).
% 0.80/1.01  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r2_hidden(esk1_2(X1,u1_struct_0(esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.80/1.01  cnf(c_0_49, plain, (r2_hidden(esk1_2(k1_tops_1(X1,X2),X3),X2)|r1_tarski(k1_tops_1(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.80/1.01  cnf(c_0_50, negated_conjecture, (r1_tarski(esk6_1(X1),esk4_0)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.80/1.01  cnf(c_0_51, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.80/1.01  cnf(c_0_52, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_28]), c_0_44])]), c_0_45])).
% 0.80/1.01  cnf(c_0_53, plain, (r1_tarski(esk2_3(X1,X2,X3),X3)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.80/1.01  cnf(c_0_54, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.80/1.01  cnf(c_0_55, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~v3_pre_topc(X2,esk3_0)|~r2_hidden(X1,X2)|~r1_tarski(X2,u1_struct_0(esk3_0))|~r1_tarski(X2,esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_31])).
% 0.80/1.01  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_tops_1(X1,esk4_0),u1_struct_0(esk3_0))|~l1_pre_topc(X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.80/1.01  fof(c_0_57, plain, ![X20, X21]:(~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|v3_pre_topc(k1_tops_1(X20,X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.80/1.01  fof(c_0_58, plain, ![X18, X19]:(~l1_pre_topc(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|m1_subset_1(k1_tops_1(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.80/1.01  cnf(c_0_59, negated_conjecture, (r1_tarski(esk6_1(X1),esk4_0)|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.80/1.01  cnf(c_0_60, plain, (v2_struct_0(X1)|r1_tarski(esk2_3(X1,X2,X3),X3)|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_53, c_0_54])).
% 0.80/1.01  cnf(c_0_61, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|v2_struct_0(X2)|~m1_connsp_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.80/1.01  cnf(c_0_62, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~v3_pre_topc(k1_tops_1(X2,esk4_0),esk3_0)|~l1_pre_topc(X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,k1_tops_1(X2,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_29])).
% 0.80/1.01  cnf(c_0_63, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.80/1.01  cnf(c_0_64, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.80/1.01  fof(c_0_65, plain, ![X28, X29, X30]:((~m1_connsp_2(X30,X28,X29)|r2_hidden(X29,k1_tops_1(X28,X30))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(~r2_hidden(X29,k1_tops_1(X28,X30))|m1_connsp_2(X30,X28,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.80/1.01  cnf(c_0_66, negated_conjecture, (r1_tarski(esk6_1(esk1_2(esk4_0,X1)),esk4_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_41])).
% 0.80/1.01  cnf(c_0_67, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X2,esk2_3(X1,X4,X3))), inference(spm,[status(thm)],[c_0_27, c_0_60])).
% 0.80/1.01  cnf(c_0_68, plain, (v2_struct_0(X1)|r2_hidden(X2,esk2_3(X1,X2,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_61, c_0_54])).
% 0.80/1.01  cnf(c_0_69, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_34]), c_0_21]), c_0_33])])).
% 0.80/1.01  cnf(c_0_70, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~v3_pre_topc(k1_tops_1(esk3_0,X2),esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,k1_tops_1(esk3_0,X2))|~r1_tarski(k1_tops_1(esk3_0,X2),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_64]), c_0_34])])).
% 0.80/1.01  cnf(c_0_71, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.80/1.01  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,esk4_0)|r1_tarski(esk4_0,X2)|~r2_hidden(X1,esk6_1(esk1_2(esk4_0,X2)))), inference(spm,[status(thm)],[c_0_27, c_0_66])).
% 0.80/1.01  cnf(c_0_73, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.80/1.01  cnf(c_0_74, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,esk1_2(k1_tops_1(esk3_0,esk4_0),X1))|r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_69, c_0_41])).
% 0.80/1.01  cnf(c_0_75, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_24, c_0_31])).
% 0.80/1.01  cnf(c_0_76, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,k1_tops_1(esk3_0,X2))|~r1_tarski(k1_tops_1(esk3_0,X2),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_63]), c_0_33]), c_0_34])])).
% 0.80/1.01  cnf(c_0_77, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_71, c_0_54])).
% 0.80/1.01  cnf(c_0_78, negated_conjecture, (r2_hidden(esk1_2(k1_tops_1(X1,esk6_1(esk1_2(esk4_0,X2))),X3),esk4_0)|r1_tarski(k1_tops_1(X1,esk6_1(esk1_2(esk4_0,X2))),X3)|r1_tarski(esk4_0,X2)|~l1_pre_topc(X1)|~m1_subset_1(esk6_1(esk1_2(esk4_0,X2)),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_72, c_0_49])).
% 0.80/1.01  cnf(c_0_79, negated_conjecture, (r2_hidden(esk1_2(k1_tops_1(esk3_0,esk4_0),X1),esk4_0)|r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)|~m1_subset_1(esk1_2(k1_tops_1(esk3_0,esk4_0),X1),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_33]), c_0_34])]), c_0_35])).
% 0.80/1.01  cnf(c_0_80, plain, (m1_subset_1(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_75, c_0_41])).
% 0.80/1.01  fof(c_0_81, plain, ![X24, X25, X26, X27]:((~v3_pre_topc(X27,X25)|k1_tops_1(X25,X27)=X27|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X25)|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(k1_tops_1(X24,X26)!=X26|v3_pre_topc(X26,X24)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X25)|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.80/1.01  cnf(c_0_82, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|~m1_connsp_2(X2,esk3_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r1_tarski(k1_tops_1(esk3_0,X2),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_33]), c_0_34])]), c_0_35])).
% 0.80/1.01  cnf(c_0_83, negated_conjecture, (r1_tarski(k1_tops_1(X1,esk6_1(esk1_2(esk4_0,X2))),esk4_0)|r1_tarski(esk4_0,X2)|~l1_pre_topc(X1)|~m1_subset_1(esk6_1(esk1_2(esk4_0,X2)),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_38, c_0_78])).
% 0.80/1.01  cnf(c_0_84, negated_conjecture, (m1_connsp_2(esk6_1(X1),esk3_0,X1)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.80/1.01  cnf(c_0_85, negated_conjecture, (r2_hidden(esk1_2(k1_tops_1(esk3_0,esk4_0),X1),esk4_0)|r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)|~r1_tarski(k1_tops_1(esk3_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.80/1.01  cnf(c_0_86, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.80/1.01  cnf(c_0_87, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|r1_tarski(esk4_0,X2)|~m1_connsp_2(esk6_1(esk1_2(esk4_0,X2)),esk3_0,X1)|~m1_subset_1(esk6_1(esk1_2(esk4_0,X2)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_34])])).
% 0.80/1.01  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_84]), c_0_33]), c_0_34])]), c_0_35]), c_0_52]), c_0_51])).
% 0.80/1.01  cnf(c_0_89, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)|~r1_tarski(k1_tops_1(esk3_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_85])).
% 0.80/1.01  cnf(c_0_90, plain, (r1_tarski(k1_tops_1(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_20, c_0_64])).
% 0.80/1.01  cnf(c_0_91, negated_conjecture, (v3_pre_topc(X1,X2)|k1_tops_1(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_21]), c_0_34])])).
% 0.80/1.01  cnf(c_0_92, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,X1)|r1_tarski(esk4_0,X2)|~m1_connsp_2(esk6_1(esk1_2(esk4_0,X2)),esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_41])).
% 0.80/1.01  cnf(c_0_93, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.80/1.01  cnf(c_0_94, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_34]), c_0_21])])).
% 0.80/1.01  cnf(c_0_95, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)!=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_21]), c_0_33]), c_0_34])]), c_0_52])).
% 0.80/1.01  cnf(c_0_96, plain, (v2_struct_0(X1)|r1_tarski(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,esk1_2(X2,k1_tops_1(X1,X3)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(X2,k1_tops_1(X1,X3)),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_38, c_0_77])).
% 0.80/1.01  cnf(c_0_97, negated_conjecture, (m1_connsp_2(esk4_0,esk3_0,esk1_2(esk4_0,X1))|r1_tarski(esk4_0,X1)|~m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_84]), c_0_52]), c_0_41])).
% 0.80/1.01  cnf(c_0_98, negated_conjecture, (~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.80/1.01  cnf(c_0_99, negated_conjecture, (~m1_subset_1(esk1_2(esk4_0,k1_tops_1(esk3_0,esk4_0)),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_33]), c_0_34])]), c_0_35]), c_0_98])).
% 0.80/1.01  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_80]), c_0_28])]), c_0_98]), ['proof']).
% 0.80/1.01  # SZS output end CNFRefutation
% 0.80/1.01  # Proof object total steps             : 101
% 0.80/1.01  # Proof object clause steps            : 74
% 0.80/1.01  # Proof object formula steps           : 27
% 0.80/1.01  # Proof object conjectures             : 45
% 0.80/1.01  # Proof object clause conjectures      : 42
% 0.80/1.01  # Proof object formula conjectures     : 3
% 0.80/1.01  # Proof object initial clauses used    : 26
% 0.80/1.01  # Proof object initial formulas used   : 13
% 0.80/1.01  # Proof object generating inferences   : 42
% 0.80/1.01  # Proof object simplifying inferences  : 66
% 0.80/1.01  # Training examples: 0 positive, 0 negative
% 0.80/1.01  # Parsed axioms                        : 13
% 0.80/1.01  # Removed by relevancy pruning/SinE    : 0
% 0.80/1.01  # Initial clauses                      : 33
% 0.80/1.01  # Removed in clause preprocessing      : 0
% 0.80/1.01  # Initial clauses in saturation        : 33
% 0.80/1.01  # Processed clauses                    : 3663
% 0.80/1.01  # ...of these trivial                  : 6
% 0.80/1.01  # ...subsumed                          : 2377
% 0.80/1.01  # ...remaining for further processing  : 1280
% 0.80/1.01  # Other redundant clauses eliminated   : 2
% 0.80/1.01  # Clauses deleted for lack of memory   : 0
% 0.80/1.01  # Backward-subsumed                    : 163
% 0.80/1.01  # Backward-rewritten                   : 18
% 0.80/1.01  # Generated clauses                    : 13721
% 0.80/1.01  # ...of the previous two non-trivial   : 12922
% 0.80/1.01  # Contextual simplify-reflections      : 198
% 0.80/1.01  # Paramodulations                      : 13719
% 0.80/1.01  # Factorizations                       : 0
% 0.80/1.01  # Equation resolutions                 : 2
% 0.80/1.01  # Propositional unsat checks           : 0
% 0.80/1.01  #    Propositional check models        : 0
% 0.80/1.01  #    Propositional check unsatisfiable : 0
% 0.80/1.01  #    Propositional clauses             : 0
% 0.80/1.01  #    Propositional clauses after purity: 0
% 0.80/1.01  #    Propositional unsat core size     : 0
% 0.80/1.01  #    Propositional preprocessing time  : 0.000
% 0.80/1.01  #    Propositional encoding time       : 0.000
% 0.80/1.01  #    Propositional solver time         : 0.000
% 0.80/1.01  #    Success case prop preproc time    : 0.000
% 0.80/1.01  #    Success case prop encoding time   : 0.000
% 0.80/1.01  #    Success case prop solver time     : 0.000
% 0.80/1.01  # Current number of processed clauses  : 1097
% 0.80/1.01  #    Positive orientable unit clauses  : 11
% 0.80/1.01  #    Positive unorientable unit clauses: 0
% 0.80/1.01  #    Negative unit clauses             : 5
% 0.80/1.01  #    Non-unit-clauses                  : 1081
% 0.80/1.01  # Current number of unprocessed clauses: 9174
% 0.80/1.01  # ...number of literals in the above   : 67163
% 0.80/1.01  # Current number of archived formulas  : 0
% 0.80/1.01  # Current number of archived clauses   : 181
% 0.80/1.01  # Clause-clause subsumption calls (NU) : 188574
% 0.80/1.01  # Rec. Clause-clause subsumption calls : 28402
% 0.80/1.01  # Non-unit clause-clause subsumptions  : 2329
% 0.80/1.01  # Unit Clause-clause subsumption calls : 436
% 0.80/1.01  # Rewrite failures with RHS unbound    : 0
% 0.80/1.01  # BW rewrite match attempts            : 11
% 0.80/1.01  # BW rewrite match successes           : 3
% 0.80/1.01  # Condensation attempts                : 0
% 0.80/1.01  # Condensation successes               : 0
% 0.80/1.01  # Termbank termtop insertions          : 426939
% 0.80/1.01  
% 0.80/1.01  # -------------------------------------------------
% 0.80/1.01  # User time                : 0.659 s
% 0.80/1.01  # System time              : 0.010 s
% 0.80/1.01  # Total time               : 0.669 s
% 0.80/1.01  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
