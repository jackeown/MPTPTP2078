%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 148 expanded)
%              Number of clauses        :   46 (  67 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 ( 594 expanded)
%              Number of equality atoms :   27 (  63 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(c_0_14,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,X29)
      | v1_xboole_0(X29)
      | r2_hidden(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_15,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X30,k1_zfmisc_1(X31))
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | m1_subset_1(X30,k1_zfmisc_1(X31)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_17,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | ~ v1_xboole_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_18,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | m1_subset_1(u1_pre_topc(X44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X44)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X24,X25] :
      ( ( r2_hidden(esk5_2(X24,X25),X24)
        | r1_tarski(k3_tarski(X24),X25) )
      & ( ~ r1_tarski(esk5_2(X24,X25),X25)
        | r1_tarski(k3_tarski(X24),X25) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X35,X36)
      | ~ r1_tarski(X36,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,plain,(
    ! [X27] : k3_tarski(k1_zfmisc_1(X27)) = X27 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_37,plain,(
    ! [X37,X38,X39,X40] :
      ( ( r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ m1_subset_1(X38,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))
        | ~ r1_tarski(X38,u1_pre_topc(X37))
        | r2_hidden(k5_setfam_1(u1_struct_0(X37),X38),u1_pre_topc(X37))
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ r2_hidden(X39,u1_pre_topc(X37))
        | ~ r2_hidden(X40,u1_pre_topc(X37))
        | r2_hidden(k9_subset_1(u1_struct_0(X37),X39,X40),u1_pre_topc(X37))
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk7_1(X37),k1_zfmisc_1(u1_struct_0(X37)))
        | m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk8_1(X37),k1_zfmisc_1(u1_struct_0(X37)))
        | m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(esk7_1(X37),u1_pre_topc(X37))
        | m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(esk8_1(X37),u1_pre_topc(X37))
        | m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X37),esk7_1(X37),esk8_1(X37)),u1_pre_topc(X37))
        | m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk7_1(X37),k1_zfmisc_1(u1_struct_0(X37)))
        | r1_tarski(esk6_1(X37),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk8_1(X37),k1_zfmisc_1(u1_struct_0(X37)))
        | r1_tarski(esk6_1(X37),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(esk7_1(X37),u1_pre_topc(X37))
        | r1_tarski(esk6_1(X37),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(esk8_1(X37),u1_pre_topc(X37))
        | r1_tarski(esk6_1(X37),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X37),esk7_1(X37),esk8_1(X37)),u1_pre_topc(X37))
        | r1_tarski(esk6_1(X37),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk7_1(X37),k1_zfmisc_1(u1_struct_0(X37)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk8_1(X37),k1_zfmisc_1(u1_struct_0(X37)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(esk7_1(X37),u1_pre_topc(X37))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(esk8_1(X37),u1_pre_topc(X37))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X37),esk7_1(X37),esk8_1(X37)),u1_pre_topc(X37))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))
        | ~ r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))
        | v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v2_pre_topc(esk9_0)
    & l1_pre_topc(esk9_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0))) != u1_struct_0(esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk9_0),k1_zfmisc_1(u1_struct_0(esk9_0)))
    | v1_xboole_0(u1_pre_topc(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk9_0),k1_zfmisc_1(u1_struct_0(esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_45])])).

fof(c_0_52,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(X13,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(esk3_2(X17,X18),X20)
        | ~ r2_hidden(X20,X17)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k1_zfmisc_1(u1_struct_0(esk9_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_54,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | r1_tarski(X22,k3_tarski(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,plain,
    ( r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_25])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_53])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk9_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_45]),c_0_57])).

cnf(c_0_62,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r2_hidden(esk5_2(X1,k3_tarski(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk9_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk9_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_42])).

fof(c_0_64,plain,(
    ! [X45] :
      ( v1_xboole_0(X45)
      | ~ r2_hidden(k3_tarski(X45),X45)
      | k4_yellow_0(k2_yellow_1(X45)) = k3_tarski(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k3_tarski(X1),u1_struct_0(esk9_0))
    | ~ r2_hidden(esk5_2(X1,u1_struct_0(esk9_0)),u1_pre_topc(esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_42]),c_0_42])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( k3_tarski(X1) = X2
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k3_tarski(u1_pre_topc(esk9_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_30])).

cnf(c_0_70,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_67,c_0_29])).

cnf(c_0_71,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk9_0)) = u1_struct_0(esk9_0)
    | ~ r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0))) != u1_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_43]),c_0_49]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:41:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.030 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.40  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.40  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.19/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.40  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.19/0.40  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.19/0.40  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.40  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.40  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.19/0.40  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.19/0.40  fof(c_0_14, plain, ![X28, X29]:(~m1_subset_1(X28,X29)|(v1_xboole_0(X29)|r2_hidden(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.40  fof(c_0_15, plain, ![X30, X31]:((~m1_subset_1(X30,k1_zfmisc_1(X31))|r1_tarski(X30,X31))&(~r1_tarski(X30,X31)|m1_subset_1(X30,k1_zfmisc_1(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.40  fof(c_0_16, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  fof(c_0_17, plain, ![X32, X33, X34]:(~r2_hidden(X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(X34))|~v1_xboole_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.40  fof(c_0_18, plain, ![X44]:(~l1_pre_topc(X44)|m1_subset_1(u1_pre_topc(X44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X44))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.40  cnf(c_0_19, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_22, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.40  fof(c_0_23, plain, ![X24, X25]:((r2_hidden(esk5_2(X24,X25),X24)|r1_tarski(k3_tarski(X24),X25))&(~r1_tarski(esk5_2(X24,X25),X25)|r1_tarski(k3_tarski(X24),X25))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.19/0.40  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_25, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_26, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|v1_xboole_0(k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.40  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.40  fof(c_0_28, plain, ![X35, X36]:(~r2_hidden(X35,X36)|~r1_tarski(X36,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.40  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_30, plain, (r2_hidden(esk5_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_31, plain, (~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))|~v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  cnf(c_0_32, plain, (r2_hidden(X1,k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.40  fof(c_0_33, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.19/0.40  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_35, plain, (r1_tarski(k3_tarski(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.40  fof(c_0_36, plain, ![X27]:k3_tarski(k1_zfmisc_1(X27))=X27, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.19/0.40  fof(c_0_37, plain, ![X37, X38, X39, X40]:((((r2_hidden(u1_struct_0(X37),u1_pre_topc(X37))|~v2_pre_topc(X37)|~l1_pre_topc(X37))&(~m1_subset_1(X38,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))|(~r1_tarski(X38,u1_pre_topc(X37))|r2_hidden(k5_setfam_1(u1_struct_0(X37),X38),u1_pre_topc(X37)))|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X37)))|(~r2_hidden(X39,u1_pre_topc(X37))|~r2_hidden(X40,u1_pre_topc(X37))|r2_hidden(k9_subset_1(u1_struct_0(X37),X39,X40),u1_pre_topc(X37))))|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(((m1_subset_1(esk7_1(X37),k1_zfmisc_1(u1_struct_0(X37)))|(m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37))&((m1_subset_1(esk8_1(X37),k1_zfmisc_1(u1_struct_0(X37)))|(m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37))&(((r2_hidden(esk7_1(X37),u1_pre_topc(X37))|(m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37))&(r2_hidden(esk8_1(X37),u1_pre_topc(X37))|(m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37)))&(~r2_hidden(k9_subset_1(u1_struct_0(X37),esk7_1(X37),esk8_1(X37)),u1_pre_topc(X37))|(m1_subset_1(esk6_1(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37))))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37)))))&(((m1_subset_1(esk7_1(X37),k1_zfmisc_1(u1_struct_0(X37)))|(r1_tarski(esk6_1(X37),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37))&((m1_subset_1(esk8_1(X37),k1_zfmisc_1(u1_struct_0(X37)))|(r1_tarski(esk6_1(X37),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37))&(((r2_hidden(esk7_1(X37),u1_pre_topc(X37))|(r1_tarski(esk6_1(X37),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37))&(r2_hidden(esk8_1(X37),u1_pre_topc(X37))|(r1_tarski(esk6_1(X37),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37)))&(~r2_hidden(k9_subset_1(u1_struct_0(X37),esk7_1(X37),esk8_1(X37)),u1_pre_topc(X37))|(r1_tarski(esk6_1(X37),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37)))))&((m1_subset_1(esk7_1(X37),k1_zfmisc_1(u1_struct_0(X37)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37))&((m1_subset_1(esk8_1(X37),k1_zfmisc_1(u1_struct_0(X37)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37))&(((r2_hidden(esk7_1(X37),u1_pre_topc(X37))|(~r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37))&(r2_hidden(esk8_1(X37),u1_pre_topc(X37))|(~r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37)))&(~r2_hidden(k9_subset_1(u1_struct_0(X37),esk7_1(X37),esk8_1(X37)),u1_pre_topc(X37))|(~r2_hidden(k5_setfam_1(u1_struct_0(X37),esk6_1(X37)),u1_pre_topc(X37))|~r2_hidden(u1_struct_0(X37),u1_pre_topc(X37)))|v2_pre_topc(X37)|~l1_pre_topc(X37)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.40  cnf(c_0_38, plain, (r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.40  cnf(c_0_39, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  fof(c_0_40, negated_conjecture, (((~v2_struct_0(esk9_0)&v2_pre_topc(esk9_0))&l1_pre_topc(esk9_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0)))!=u1_struct_0(esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).
% 0.19/0.40  cnf(c_0_41, plain, (~r2_hidden(X1,k3_tarski(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.40  cnf(c_0_42, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.40  cnf(c_0_43, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_44, plain, (r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|v1_xboole_0(u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (l1_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.40  cnf(c_0_46, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.40  cnf(c_0_47, plain, (~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_29, c_0_43])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (r2_hidden(u1_struct_0(esk9_0),k1_zfmisc_1(u1_struct_0(esk9_0)))|v1_xboole_0(u1_pre_topc(esk9_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (v2_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.40  cnf(c_0_50, plain, (r2_hidden(X1,k1_zfmisc_1(X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (r2_hidden(u1_struct_0(esk9_0),k1_zfmisc_1(u1_struct_0(esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_45])])).
% 0.19/0.40  fof(c_0_52, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:((((r2_hidden(X13,esk2_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k3_tarski(X11))&(r2_hidden(esk2_3(X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k3_tarski(X11)))&(~r2_hidden(X15,X16)|~r2_hidden(X16,X11)|r2_hidden(X15,X12)|X12!=k3_tarski(X11)))&((~r2_hidden(esk3_2(X17,X18),X18)|(~r2_hidden(esk3_2(X17,X18),X20)|~r2_hidden(X20,X17))|X18=k3_tarski(X17))&((r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))&(r2_hidden(esk4_2(X17,X18),X17)|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (r2_hidden(k1_zfmisc_1(u1_struct_0(esk9_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0))))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.40  fof(c_0_54, plain, ![X22, X23]:(~r2_hidden(X22,X23)|r1_tarski(X22,k3_tarski(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.19/0.40  cnf(c_0_55, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.40  cnf(c_0_56, plain, (r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_25])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0))))), inference(spm,[status(thm)],[c_0_29, c_0_53])).
% 0.19/0.40  cnf(c_0_58, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk5_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_59, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.40  cnf(c_0_60, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (r2_hidden(u1_pre_topc(esk9_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_45]), c_0_57])).
% 0.19/0.40  cnf(c_0_62, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r2_hidden(esk5_2(X1,k3_tarski(X2)),X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk9_0)))|~r2_hidden(X1,u1_pre_topc(esk9_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_42])).
% 0.19/0.40  fof(c_0_64, plain, ![X45]:(v1_xboole_0(X45)|(~r2_hidden(k3_tarski(X45),X45)|k4_yellow_0(k2_yellow_1(X45))=k3_tarski(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.19/0.40  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (r1_tarski(k3_tarski(X1),u1_struct_0(esk9_0))|~r2_hidden(esk5_2(X1,u1_struct_0(esk9_0)),u1_pre_topc(esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_42]), c_0_42])).
% 0.19/0.40  cnf(c_0_67, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.40  cnf(c_0_68, plain, (k3_tarski(X1)=X2|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_65, c_0_59])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (r1_tarski(k3_tarski(u1_pre_topc(esk9_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_66, c_0_30])).
% 0.19/0.40  cnf(c_0_70, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_67, c_0_29])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (k3_tarski(u1_pre_topc(esk9_0))=u1_struct_0(esk9_0)|~r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0)))!=u1_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (~r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_43]), c_0_49]), c_0_45])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 75
% 0.19/0.40  # Proof object clause steps            : 46
% 0.19/0.40  # Proof object formula steps           : 29
% 0.19/0.40  # Proof object conjectures             : 17
% 0.19/0.40  # Proof object clause conjectures      : 14
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 19
% 0.19/0.40  # Proof object initial formulas used   : 14
% 0.19/0.40  # Proof object generating inferences   : 24
% 0.19/0.40  # Proof object simplifying inferences  : 14
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 14
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 44
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 44
% 0.19/0.40  # Processed clauses                    : 382
% 0.19/0.40  # ...of these trivial                  : 1
% 0.19/0.40  # ...subsumed                          : 116
% 0.19/0.40  # ...remaining for further processing  : 265
% 0.19/0.40  # Other redundant clauses eliminated   : 5
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 1
% 0.19/0.40  # Backward-rewritten                   : 1
% 0.19/0.40  # Generated clauses                    : 914
% 0.19/0.40  # ...of the previous two non-trivial   : 864
% 0.19/0.40  # Contextual simplify-reflections      : 1
% 0.19/0.40  # Paramodulations                      : 909
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 5
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 215
% 0.19/0.40  #    Positive orientable unit clauses  : 11
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 8
% 0.19/0.40  #    Non-unit-clauses                  : 196
% 0.19/0.40  # Current number of unprocessed clauses: 567
% 0.19/0.40  # ...number of literals in the above   : 1693
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 45
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 5025
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 2324
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 90
% 0.19/0.40  # Unit Clause-clause subsumption calls : 36
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 13
% 0.19/0.40  # BW rewrite match successes           : 1
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 17086
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.058 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.062 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
