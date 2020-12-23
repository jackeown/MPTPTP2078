%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 (1774 expanded)
%              Number of clauses        :   63 ( 861 expanded)
%              Number of leaves         :   12 ( 423 expanded)
%              Depth                    :   24
%              Number of atoms          :  341 (7955 expanded)
%              Number of equality atoms :   34 ( 919 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X31,X32,X33] :
      ( ~ r2_hidden(X31,X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X33))
      | ~ v1_xboole_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_16,plain,(
    ! [X41] :
      ( ~ l1_pre_topc(X41)
      | m1_subset_1(u1_pre_topc(X41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X41)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X26,X25)
        | r2_hidden(X26,X25)
        | v1_xboole_0(X25) )
      & ( ~ r2_hidden(X26,X25)
        | m1_subset_1(X26,X25)
        | v1_xboole_0(X25) )
      & ( ~ m1_subset_1(X26,X25)
        | v1_xboole_0(X26)
        | ~ v1_xboole_0(X25) )
      & ( ~ v1_xboole_0(X26)
        | m1_subset_1(X26,X25)
        | ~ v1_xboole_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(X15,esk2_3(X13,X14,X15))
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( r2_hidden(esk2_3(X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X18,X13)
        | r2_hidden(X17,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r2_hidden(esk3_2(X19,X20),X22)
        | ~ r2_hidden(X22,X19)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk4_2(X19,X20),X19)
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_25,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X34,X35,X36,X37] :
      ( ( r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ r1_tarski(X35,u1_pre_topc(X34))
        | r2_hidden(k5_setfam_1(u1_struct_0(X34),X35),u1_pre_topc(X34))
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ r2_hidden(X36,u1_pre_topc(X34))
        | ~ r2_hidden(X37,u1_pre_topc(X34))
        | r2_hidden(k9_subset_1(u1_struct_0(X34),X36,X37),u1_pre_topc(X34))
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk6_1(X34),k1_zfmisc_1(u1_struct_0(X34)))
        | m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk7_1(X34),k1_zfmisc_1(u1_struct_0(X34)))
        | m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(esk6_1(X34),u1_pre_topc(X34))
        | m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(esk7_1(X34),u1_pre_topc(X34))
        | m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X34),esk6_1(X34),esk7_1(X34)),u1_pre_topc(X34))
        | m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk6_1(X34),k1_zfmisc_1(u1_struct_0(X34)))
        | r1_tarski(esk5_1(X34),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk7_1(X34),k1_zfmisc_1(u1_struct_0(X34)))
        | r1_tarski(esk5_1(X34),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(esk6_1(X34),u1_pre_topc(X34))
        | r1_tarski(esk5_1(X34),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(esk7_1(X34),u1_pre_topc(X34))
        | r1_tarski(esk5_1(X34),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X34),esk6_1(X34),esk7_1(X34)),u1_pre_topc(X34))
        | r1_tarski(esk5_1(X34),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk6_1(X34),k1_zfmisc_1(u1_struct_0(X34)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk7_1(X34),k1_zfmisc_1(u1_struct_0(X34)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(esk6_1(X34),u1_pre_topc(X34))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(esk7_1(X34),u1_pre_topc(X34))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X34),esk6_1(X34),esk7_1(X34)),u1_pre_topc(X34))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))
        | ~ r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))
        | v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v2_pre_topc(esk8_0)
    & l1_pre_topc(esk8_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0))) != u1_struct_0(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X24] : k3_tarski(k1_zfmisc_1(X24)) = X24 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(u1_pre_topc(X1),X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(u1_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_pre_topc(X1),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | r1_tarski(u1_pre_topc(esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | r2_hidden(u1_struct_0(esk8_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_40])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(ef,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k1_zfmisc_1(u1_struct_0(esk8_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk8_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk8_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_40]),c_0_53])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk8_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_42])).

fof(c_0_58,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27)))
      | k5_setfam_1(X27,X28) = k3_tarski(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ r2_hidden(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk8_0))),u1_pre_topc(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_61,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_32])).

fof(c_0_63,plain,(
    ! [X42] :
      ( v1_xboole_0(X42)
      | ~ r2_hidden(k3_tarski(X42),X42)
      | k4_yellow_0(k2_yellow_1(X42)) = k3_tarski(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,plain,
    ( r2_hidden(k3_tarski(X1),u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk8_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_62])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( r2_hidden(u1_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_64])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_65,c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k3_tarski(u1_pre_topc(esk8_0)),u1_pre_topc(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_45]),c_0_40]),c_0_19])])).

cnf(c_0_72,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_68,c_0_34])).

cnf(c_0_73,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(esk3_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_74,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_75,plain,
    ( r2_hidden(u1_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk8_0),k1_zfmisc_1(u1_pre_topc(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0))) != u1_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_78,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0))) = k3_tarski(u1_pre_topc(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_71])).

cnf(c_0_79,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk4_2(X2,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk8_0),u1_pre_topc(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_45]),c_0_40])])).

cnf(c_0_81,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk8_0)) != u1_struct_0(esk8_0) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X2,u1_pre_topc(esk8_0))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_57]),c_0_42])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk4_2(u1_pre_topc(esk8_0),u1_struct_0(esk8_0)),u1_pre_topc(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,esk4_2(u1_pre_topc(esk8_0),u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_85,plain,
    ( r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk3_2(u1_pre_topc(esk8_0),u1_struct_0(esk8_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_86]),c_0_86]),c_0_80])]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.51  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.029 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.51  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.51  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.51  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.51  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.51  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.51  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.51  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.19/0.51  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.51  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.19/0.51  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.19/0.51  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.19/0.51  fof(c_0_12, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.51  fof(c_0_13, plain, ![X29, X30]:((~m1_subset_1(X29,k1_zfmisc_1(X30))|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|m1_subset_1(X29,k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.51  cnf(c_0_14, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.51  fof(c_0_15, plain, ![X31, X32, X33]:(~r2_hidden(X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(X33))|~v1_xboole_0(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.51  fof(c_0_16, plain, ![X41]:(~l1_pre_topc(X41)|m1_subset_1(u1_pre_topc(X41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X41))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.51  fof(c_0_17, plain, ![X25, X26]:(((~m1_subset_1(X26,X25)|r2_hidden(X26,X25)|v1_xboole_0(X25))&(~r2_hidden(X26,X25)|m1_subset_1(X26,X25)|v1_xboole_0(X25)))&((~m1_subset_1(X26,X25)|v1_xboole_0(X26)|~v1_xboole_0(X25))&(~v1_xboole_0(X26)|m1_subset_1(X26,X25)|~v1_xboole_0(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.51  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.51  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.51  cnf(c_0_21, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.51  cnf(c_0_22, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.51  fof(c_0_24, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.51  cnf(c_0_25, plain, (~l1_pre_topc(X1)|~v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.51  cnf(c_0_26, plain, (v1_xboole_0(k1_zfmisc_1(X1))|r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.51  fof(c_0_27, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.51  fof(c_0_28, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.19/0.51  cnf(c_0_29, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  fof(c_0_30, plain, ![X34, X35, X36, X37]:((((r2_hidden(u1_struct_0(X34),u1_pre_topc(X34))|~v2_pre_topc(X34)|~l1_pre_topc(X34))&(~m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))|(~r1_tarski(X35,u1_pre_topc(X34))|r2_hidden(k5_setfam_1(u1_struct_0(X34),X35),u1_pre_topc(X34)))|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))|(~r2_hidden(X36,u1_pre_topc(X34))|~r2_hidden(X37,u1_pre_topc(X34))|r2_hidden(k9_subset_1(u1_struct_0(X34),X36,X37),u1_pre_topc(X34))))|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(((m1_subset_1(esk6_1(X34),k1_zfmisc_1(u1_struct_0(X34)))|(m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34))&((m1_subset_1(esk7_1(X34),k1_zfmisc_1(u1_struct_0(X34)))|(m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34))&(((r2_hidden(esk6_1(X34),u1_pre_topc(X34))|(m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34))&(r2_hidden(esk7_1(X34),u1_pre_topc(X34))|(m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34)))&(~r2_hidden(k9_subset_1(u1_struct_0(X34),esk6_1(X34),esk7_1(X34)),u1_pre_topc(X34))|(m1_subset_1(esk5_1(X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34)))))&(((m1_subset_1(esk6_1(X34),k1_zfmisc_1(u1_struct_0(X34)))|(r1_tarski(esk5_1(X34),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34))&((m1_subset_1(esk7_1(X34),k1_zfmisc_1(u1_struct_0(X34)))|(r1_tarski(esk5_1(X34),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34))&(((r2_hidden(esk6_1(X34),u1_pre_topc(X34))|(r1_tarski(esk5_1(X34),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34))&(r2_hidden(esk7_1(X34),u1_pre_topc(X34))|(r1_tarski(esk5_1(X34),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34)))&(~r2_hidden(k9_subset_1(u1_struct_0(X34),esk6_1(X34),esk7_1(X34)),u1_pre_topc(X34))|(r1_tarski(esk5_1(X34),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34)))))&((m1_subset_1(esk6_1(X34),k1_zfmisc_1(u1_struct_0(X34)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34))&((m1_subset_1(esk7_1(X34),k1_zfmisc_1(u1_struct_0(X34)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34))&(((r2_hidden(esk6_1(X34),u1_pre_topc(X34))|(~r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34))&(r2_hidden(esk7_1(X34),u1_pre_topc(X34))|(~r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34)))&(~r2_hidden(k9_subset_1(u1_struct_0(X34),esk6_1(X34),esk7_1(X34)),u1_pre_topc(X34))|(~r2_hidden(k5_setfam_1(u1_struct_0(X34),esk5_1(X34)),u1_pre_topc(X34))|~r2_hidden(u1_struct_0(X34),u1_pre_topc(X34)))|v2_pre_topc(X34)|~l1_pre_topc(X34)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.51  cnf(c_0_31, plain, (r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.51  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.51  fof(c_0_33, negated_conjecture, (((~v2_struct_0(esk8_0)&v2_pre_topc(esk8_0))&l1_pre_topc(esk8_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0)))!=u1_struct_0(esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).
% 0.19/0.51  cnf(c_0_34, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_23])).
% 0.19/0.51  cnf(c_0_35, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.51  fof(c_0_36, plain, ![X24]:k3_tarski(k1_zfmisc_1(X24))=X24, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.19/0.51  cnf(c_0_37, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.51  cnf(c_0_38, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.51  cnf(c_0_39, plain, (r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|r1_tarski(u1_pre_topc(X1),X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.51  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.51  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.51  cnf(c_0_42, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.51  cnf(c_0_43, plain, (r2_hidden(u1_struct_0(X1),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r1_tarski(u1_pre_topc(X1),X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.51  cnf(c_0_44, negated_conjecture, (r2_hidden(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))|r1_tarski(u1_pre_topc(esk8_0),X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.51  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.51  cnf(c_0_46, plain, (~v1_xboole_0(k1_zfmisc_1(X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.51  cnf(c_0_47, negated_conjecture, (r2_hidden(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))|r2_hidden(u1_struct_0(esk8_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_40])])).
% 0.19/0.51  cnf(c_0_48, plain, (r2_hidden(X1,k1_zfmisc_1(X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_26])).
% 0.19/0.51  cnf(c_0_49, negated_conjecture, (r2_hidden(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(ef,[status(thm)],[c_0_47])).
% 0.19/0.51  cnf(c_0_50, negated_conjecture, (r2_hidden(k1_zfmisc_1(u1_struct_0(esk8_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk8_0))))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.51  cnf(c_0_51, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  cnf(c_0_52, plain, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.51  cnf(c_0_53, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk8_0))))), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 0.19/0.51  cnf(c_0_54, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_51])).
% 0.19/0.51  cnf(c_0_55, negated_conjecture, (r2_hidden(u1_pre_topc(esk8_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk8_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_40]), c_0_53])).
% 0.19/0.51  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.51  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))|~r2_hidden(X1,u1_pre_topc(esk8_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_42])).
% 0.19/0.51  fof(c_0_58, plain, ![X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27)))|k5_setfam_1(X27,X28)=k3_tarski(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.19/0.51  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))|~r2_hidden(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk8_0))),u1_pre_topc(esk8_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.51  cnf(c_0_60, plain, (r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.51  cnf(c_0_61, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.51  cnf(c_0_62, negated_conjecture, (r1_tarski(u1_pre_topc(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_59, c_0_32])).
% 0.19/0.51  fof(c_0_63, plain, ![X42]:(v1_xboole_0(X42)|(~r2_hidden(k3_tarski(X42),X42)|k4_yellow_0(k2_yellow_1(X42))=k3_tarski(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.19/0.51  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.51  cnf(c_0_65, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_66, plain, (r2_hidden(k3_tarski(X1),u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.51  cnf(c_0_67, negated_conjecture, (m1_subset_1(u1_pre_topc(esk8_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk8_0))))), inference(spm,[status(thm)],[c_0_18, c_0_62])).
% 0.19/0.51  cnf(c_0_68, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.51  cnf(c_0_69, plain, (r2_hidden(u1_struct_0(X1),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_43, c_0_64])).
% 0.19/0.51  cnf(c_0_70, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_65, c_0_34])).
% 0.19/0.51  cnf(c_0_71, negated_conjecture, (r2_hidden(k3_tarski(u1_pre_topc(esk8_0)),u1_pre_topc(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_45]), c_0_40]), c_0_19])])).
% 0.19/0.51  cnf(c_0_72, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_68, c_0_34])).
% 0.19/0.51  cnf(c_0_73, plain, (X2=k3_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(esk3_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  cnf(c_0_74, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  cnf(c_0_75, plain, (r2_hidden(u1_struct_0(X1),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.51  cnf(c_0_76, negated_conjecture, (r2_hidden(u1_pre_topc(esk8_0),k1_zfmisc_1(u1_pre_topc(esk8_0)))), inference(spm,[status(thm)],[c_0_48, c_0_71])).
% 0.19/0.51  cnf(c_0_77, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0)))!=u1_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.51  cnf(c_0_78, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0)))=k3_tarski(u1_pre_topc(esk8_0))), inference(spm,[status(thm)],[c_0_72, c_0_71])).
% 0.19/0.51  cnf(c_0_79, plain, (X1=k3_tarski(X2)|r2_hidden(esk4_2(X2,X1),X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_74])).
% 0.19/0.51  cnf(c_0_80, negated_conjecture, (r2_hidden(u1_struct_0(esk8_0),u1_pre_topc(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_45]), c_0_40])])).
% 0.19/0.51  cnf(c_0_81, negated_conjecture, (k3_tarski(u1_pre_topc(esk8_0))!=u1_struct_0(esk8_0)), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.51  cnf(c_0_82, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk8_0))|~r2_hidden(X2,u1_pre_topc(esk8_0))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_57]), c_0_42])).
% 0.19/0.51  cnf(c_0_83, negated_conjecture, (r2_hidden(esk4_2(u1_pre_topc(esk8_0),u1_struct_0(esk8_0)),u1_pre_topc(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.19/0.51  cnf(c_0_84, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk8_0))|~r2_hidden(X1,esk4_2(u1_pre_topc(esk8_0),u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.51  cnf(c_0_85, plain, (r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  cnf(c_0_86, negated_conjecture, (r2_hidden(esk3_2(u1_pre_topc(esk8_0),u1_struct_0(esk8_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_81])).
% 0.19/0.51  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_86]), c_0_86]), c_0_80])]), c_0_81]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 88
% 0.19/0.51  # Proof object clause steps            : 63
% 0.19/0.51  # Proof object formula steps           : 25
% 0.19/0.51  # Proof object conjectures             : 26
% 0.19/0.51  # Proof object clause conjectures      : 23
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 23
% 0.19/0.51  # Proof object initial formulas used   : 12
% 0.19/0.51  # Proof object generating inferences   : 34
% 0.19/0.51  # Proof object simplifying inferences  : 26
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 12
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 45
% 0.19/0.51  # Removed in clause preprocessing      : 0
% 0.19/0.51  # Initial clauses in saturation        : 45
% 0.19/0.51  # Processed clauses                    : 1400
% 0.19/0.51  # ...of these trivial                  : 6
% 0.19/0.51  # ...subsumed                          : 717
% 0.19/0.51  # ...remaining for further processing  : 677
% 0.19/0.51  # Other redundant clauses eliminated   : 7
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 16
% 0.19/0.51  # Backward-rewritten                   : 17
% 0.19/0.51  # Generated clauses                    : 8099
% 0.19/0.51  # ...of the previous two non-trivial   : 7665
% 0.19/0.51  # Contextual simplify-reflections      : 5
% 0.19/0.51  # Paramodulations                      : 8086
% 0.19/0.51  # Factorizations                       : 6
% 0.19/0.51  # Equation resolutions                 : 7
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 595
% 0.19/0.51  #    Positive orientable unit clauses  : 23
% 0.19/0.51  #    Positive unorientable unit clauses: 0
% 0.19/0.51  #    Negative unit clauses             : 8
% 0.19/0.51  #    Non-unit-clauses                  : 564
% 0.19/0.51  # Current number of unprocessed clauses: 6300
% 0.19/0.51  # ...number of literals in the above   : 27231
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 77
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 38327
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 15550
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 704
% 0.19/0.51  # Unit Clause-clause subsumption calls : 127
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 52
% 0.19/0.51  # BW rewrite match successes           : 6
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 128627
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.162 s
% 0.19/0.51  # System time              : 0.012 s
% 0.19/0.51  # Total time               : 0.174 s
% 0.19/0.51  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
