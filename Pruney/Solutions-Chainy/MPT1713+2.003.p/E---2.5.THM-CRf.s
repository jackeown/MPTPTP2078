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
% DateTime   : Thu Dec  3 11:16:54 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 181 expanded)
%              Number of clauses        :   48 (  78 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  268 ( 702 expanded)
%              Number of equality atoms :   28 (  59 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t22_tmap_1,conjecture,(
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
             => ( m1_pre_topc(X2,X3)
               => ( ~ r1_tsep_1(X2,X3)
                  & ~ r1_tsep_1(X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_16,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_17,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k3_xboole_0(X13,X14) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

fof(c_0_24,plain,(
    ! [X19,X20] :
      ( ( ~ r1_xboole_0(X19,X20)
        | k4_xboole_0(X19,X20) = X19 )
      & ( k4_xboole_0(X19,X20) != X19
        | r1_xboole_0(X19,X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_25,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | ~ r1_tarski(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_26,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X18] : r1_xboole_0(X18,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X1) = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_33])])).

fof(c_0_36,plain,(
    ! [X24,X25,X26,X28,X30] :
      ( ( r1_tarski(k2_struct_0(X25),k2_struct_0(X24))
        | ~ m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk2_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))
        | ~ r2_hidden(X26,u1_pre_topc(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(esk2_3(X24,X25,X26),u1_pre_topc(X24))
        | ~ r2_hidden(X26,u1_pre_topc(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) )
      & ( X26 = k9_subset_1(u1_struct_0(X25),esk2_3(X24,X25,X26),k2_struct_0(X25))
        | ~ r2_hidden(X26,u1_pre_topc(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) )
      & ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ r2_hidden(X28,u1_pre_topc(X24))
        | X26 != k9_subset_1(u1_struct_0(X25),X28,k2_struct_0(X25))
        | r2_hidden(X26,u1_pre_topc(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk3_2(X24,X25),k1_zfmisc_1(u1_struct_0(X25)))
        | ~ r1_tarski(k2_struct_0(X25),k2_struct_0(X24))
        | m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) )
      & ( ~ r2_hidden(esk3_2(X24,X25),u1_pre_topc(X25))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ r2_hidden(X30,u1_pre_topc(X24))
        | esk3_2(X24,X25) != k9_subset_1(u1_struct_0(X25),X30,k2_struct_0(X25))
        | ~ r1_tarski(k2_struct_0(X25),k2_struct_0(X24))
        | m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk4_2(X24,X25),k1_zfmisc_1(u1_struct_0(X24)))
        | r2_hidden(esk3_2(X24,X25),u1_pre_topc(X25))
        | ~ r1_tarski(k2_struct_0(X25),k2_struct_0(X24))
        | m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(esk4_2(X24,X25),u1_pre_topc(X24))
        | r2_hidden(esk3_2(X24,X25),u1_pre_topc(X25))
        | ~ r1_tarski(k2_struct_0(X25),k2_struct_0(X24))
        | m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) )
      & ( esk3_2(X24,X25) = k9_subset_1(u1_struct_0(X25),esk4_2(X24,X25),k2_struct_0(X25))
        | r2_hidden(esk3_2(X24,X25),u1_pre_topc(X25))
        | ~ r1_tarski(k2_struct_0(X25),k2_struct_0(X24))
        | m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_37,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_pre_topc(X34,X33)
      | l1_pre_topc(X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_38,plain,(
    ! [X23] :
      ( ~ l1_struct_0(X23)
      | k2_struct_0(X23) = u1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_39,plain,(
    ! [X32] :
      ( ~ l1_pre_topc(X32)
      | l1_struct_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_40,negated_conjecture,(
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
               => ( m1_pre_topc(X2,X3)
                 => ( ~ r1_tsep_1(X2,X3)
                    & ~ r1_tsep_1(X3,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_tmap_1])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,k4_xboole_0(X2,X1))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X38,X39] :
      ( ~ l1_struct_0(X38)
      | ~ l1_struct_0(X39)
      | ~ r1_tsep_1(X38,X39)
      | r1_tsep_1(X39,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk5_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk5_0)
    & m1_pre_topc(esk6_0,esk7_0)
    & ( r1_tsep_1(esk6_0,esk7_0)
      | r1_tsep_1(esk7_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])).

cnf(c_0_49,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk7_0)
    | r1_tsep_1(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X1)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_23])).

cnf(c_0_55,plain,
    ( r1_tarski(u1_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_44])).

fof(c_0_56,plain,(
    ! [X36,X37] :
      ( ( ~ r1_tsep_1(X36,X37)
        | r1_xboole_0(u1_struct_0(X36),u1_struct_0(X37))
        | ~ l1_struct_0(X37)
        | ~ l1_struct_0(X36) )
      & ( ~ r1_xboole_0(u1_struct_0(X36),u1_struct_0(X37))
        | r1_tsep_1(X36,X37)
        | ~ l1_struct_0(X37)
        | ~ l1_struct_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk7_0)
    | ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_58,plain,(
    ! [X35] :
      ( v2_struct_0(X35)
      | ~ l1_struct_0(X35)
      | ~ v1_xboole_0(u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_59,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_60,plain,
    ( ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_xboole_0(k2_struct_0(X2),u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0)
    | ~ l1_struct_0(esk7_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_70,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_63]),c_0_64])])).

cnf(c_0_71,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(esk7_0)
    | ~ r2_hidden(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70])])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_71]),c_0_64])])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_46])).

cnf(c_0_76,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_77,negated_conjecture,
    ( ~ l1_struct_0(esk7_0)
    | ~ r2_hidden(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_46]),c_0_74])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk1_1(u1_struct_0(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_74]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_46]),c_0_70])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_78,c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.028 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.47  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.47  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.47  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.47  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.47  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.47  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.47  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.20/0.47  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.47  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.47  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.47  fof(t22_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(m1_pre_topc(X2,X3)=>(~(r1_tsep_1(X2,X3))&~(r1_tsep_1(X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 0.20/0.47  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.20/0.47  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.20/0.47  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.47  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.47  fof(c_0_16, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.47  fof(c_0_17, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.47  fof(c_0_18, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k3_xboole_0(X13,X14)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.47  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.47  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20])).
% 0.20/0.47  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.20/0.47  fof(c_0_24, plain, ![X19, X20]:((~r1_xboole_0(X19,X20)|k4_xboole_0(X19,X20)=X19)&(k4_xboole_0(X19,X20)!=X19|r1_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.47  fof(c_0_25, plain, ![X21, X22]:(~r2_hidden(X21,X22)|~r1_tarski(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.47  fof(c_0_26, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.47  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.47  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.47  fof(c_0_29, plain, ![X18]:r1_xboole_0(X18,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.47  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.47  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_32, plain, (k4_xboole_0(X1,X1)=X2|~r1_tarski(X2,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.47  cnf(c_0_33, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.47  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.47  cnf(c_0_35, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_33])])).
% 0.20/0.47  fof(c_0_36, plain, ![X24, X25, X26, X28, X30]:(((r1_tarski(k2_struct_0(X25),k2_struct_0(X24))|~m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24))&((((m1_subset_1(esk2_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))|~r2_hidden(X26,u1_pre_topc(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24))&(r2_hidden(esk2_3(X24,X25,X26),u1_pre_topc(X24))|~r2_hidden(X26,u1_pre_topc(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24)))&(X26=k9_subset_1(u1_struct_0(X25),esk2_3(X24,X25,X26),k2_struct_0(X25))|~r2_hidden(X26,u1_pre_topc(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24)))&(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X24)))|~r2_hidden(X28,u1_pre_topc(X24))|X26!=k9_subset_1(u1_struct_0(X25),X28,k2_struct_0(X25))|r2_hidden(X26,u1_pre_topc(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24))))&((m1_subset_1(esk3_2(X24,X25),k1_zfmisc_1(u1_struct_0(X25)))|~r1_tarski(k2_struct_0(X25),k2_struct_0(X24))|m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24))&((~r2_hidden(esk3_2(X24,X25),u1_pre_topc(X25))|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X24)))|~r2_hidden(X30,u1_pre_topc(X24))|esk3_2(X24,X25)!=k9_subset_1(u1_struct_0(X25),X30,k2_struct_0(X25)))|~r1_tarski(k2_struct_0(X25),k2_struct_0(X24))|m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24))&(((m1_subset_1(esk4_2(X24,X25),k1_zfmisc_1(u1_struct_0(X24)))|r2_hidden(esk3_2(X24,X25),u1_pre_topc(X25))|~r1_tarski(k2_struct_0(X25),k2_struct_0(X24))|m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24))&(r2_hidden(esk4_2(X24,X25),u1_pre_topc(X24))|r2_hidden(esk3_2(X24,X25),u1_pre_topc(X25))|~r1_tarski(k2_struct_0(X25),k2_struct_0(X24))|m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24)))&(esk3_2(X24,X25)=k9_subset_1(u1_struct_0(X25),esk4_2(X24,X25),k2_struct_0(X25))|r2_hidden(esk3_2(X24,X25),u1_pre_topc(X25))|~r1_tarski(k2_struct_0(X25),k2_struct_0(X24))|m1_pre_topc(X25,X24)|~l1_pre_topc(X25)|~l1_pre_topc(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.20/0.47  fof(c_0_37, plain, ![X33, X34]:(~l1_pre_topc(X33)|(~m1_pre_topc(X34,X33)|l1_pre_topc(X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.47  fof(c_0_38, plain, ![X23]:(~l1_struct_0(X23)|k2_struct_0(X23)=u1_struct_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.47  fof(c_0_39, plain, ![X32]:(~l1_pre_topc(X32)|l1_struct_0(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.47  fof(c_0_40, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(m1_pre_topc(X2,X3)=>(~(r1_tsep_1(X2,X3))&~(r1_tsep_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t22_tmap_1])).
% 0.20/0.47  cnf(c_0_41, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.47  cnf(c_0_42, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,k4_xboole_0(X2,X1))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 0.20/0.47  cnf(c_0_43, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_44, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.47  cnf(c_0_45, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.47  cnf(c_0_46, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.47  fof(c_0_47, plain, ![X38, X39]:(~l1_struct_0(X38)|~l1_struct_0(X39)|(~r1_tsep_1(X38,X39)|r1_tsep_1(X39,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.20/0.47  fof(c_0_48, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk5_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk5_0))&(m1_pre_topc(esk6_0,esk7_0)&(r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])).
% 0.20/0.47  cnf(c_0_49, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k4_xboole_0(X2,k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.47  cnf(c_0_50, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.47  cnf(c_0_51, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.47  cnf(c_0_52, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.47  cnf(c_0_53, negated_conjecture, (r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.47  cnf(c_0_54, plain, (~r1_tarski(X1,X2)|~r1_xboole_0(X2,X1)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_49, c_0_23])).
% 0.20/0.47  cnf(c_0_55, plain, (r1_tarski(u1_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_44])).
% 0.20/0.47  fof(c_0_56, plain, ![X36, X37]:((~r1_tsep_1(X36,X37)|r1_xboole_0(u1_struct_0(X36),u1_struct_0(X37))|~l1_struct_0(X37)|~l1_struct_0(X36))&(~r1_xboole_0(u1_struct_0(X36),u1_struct_0(X37))|r1_tsep_1(X36,X37)|~l1_struct_0(X37)|~l1_struct_0(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.20/0.47  cnf(c_0_57, negated_conjecture, (r1_tsep_1(esk6_0,esk7_0)|~l1_struct_0(esk6_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.47  fof(c_0_58, plain, ![X35]:(v2_struct_0(X35)|~l1_struct_0(X35)|~v1_xboole_0(u1_struct_0(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.47  fof(c_0_59, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.47  cnf(c_0_60, plain, (~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r1_xboole_0(k2_struct_0(X2),u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.47  cnf(c_0_61, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.47  cnf(c_0_62, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)|~l1_struct_0(esk7_0)|~l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_57])).
% 0.20/0.47  cnf(c_0_63, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.47  cnf(c_0_64, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.47  cnf(c_0_65, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.47  cnf(c_0_66, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.47  cnf(c_0_67, plain, (~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r1_xboole_0(u1_struct_0(X2),u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_60, c_0_51])).
% 0.20/0.47  cnf(c_0_68, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))|~l1_struct_0(esk6_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.47  cnf(c_0_69, negated_conjecture, (m1_pre_topc(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.47  cnf(c_0_70, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_63]), c_0_64])])).
% 0.20/0.47  cnf(c_0_71, negated_conjecture, (m1_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.47  cnf(c_0_72, plain, (v2_struct_0(X1)|r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(X1))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.47  cnf(c_0_73, negated_conjecture, (~l1_struct_0(esk6_0)|~l1_struct_0(esk7_0)|~r2_hidden(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70])])).
% 0.20/0.47  cnf(c_0_74, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_71]), c_0_64])])).
% 0.20/0.47  cnf(c_0_75, plain, (v2_struct_0(X1)|r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_72, c_0_46])).
% 0.20/0.47  cnf(c_0_76, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.47  cnf(c_0_77, negated_conjecture, (~l1_struct_0(esk7_0)|~r2_hidden(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_46]), c_0_74])])).
% 0.20/0.47  cnf(c_0_78, negated_conjecture, (r2_hidden(esk1_1(u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_74]), c_0_76])).
% 0.20/0.47  cnf(c_0_79, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_46]), c_0_70])])).
% 0.20/0.47  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_78, c_0_79]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 81
% 0.20/0.47  # Proof object clause steps            : 48
% 0.20/0.47  # Proof object formula steps           : 33
% 0.20/0.47  # Proof object conjectures             : 19
% 0.20/0.47  # Proof object clause conjectures      : 16
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 21
% 0.20/0.47  # Proof object initial formulas used   : 16
% 0.20/0.47  # Proof object generating inferences   : 23
% 0.20/0.47  # Proof object simplifying inferences  : 20
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 17
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 37
% 0.20/0.47  # Removed in clause preprocessing      : 1
% 0.20/0.47  # Initial clauses in saturation        : 36
% 0.20/0.47  # Processed clauses                    : 1918
% 0.20/0.47  # ...of these trivial                  : 17
% 0.20/0.47  # ...subsumed                          : 1581
% 0.20/0.47  # ...remaining for further processing  : 320
% 0.20/0.47  # Other redundant clauses eliminated   : 57
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 26
% 0.20/0.47  # Backward-rewritten                   : 7
% 0.20/0.47  # Generated clauses                    : 6805
% 0.20/0.47  # ...of the previous two non-trivial   : 5467
% 0.20/0.47  # Contextual simplify-reflections      : 15
% 0.20/0.47  # Paramodulations                      : 6747
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 57
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 249
% 0.20/0.47  #    Positive orientable unit clauses  : 18
% 0.20/0.47  #    Positive unorientable unit clauses: 4
% 0.20/0.47  #    Negative unit clauses             : 21
% 0.20/0.47  #    Non-unit-clauses                  : 206
% 0.20/0.47  # Current number of unprocessed clauses: 3479
% 0.20/0.47  # ...number of literals in the above   : 11904
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 71
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 21872
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 10324
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 1095
% 0.20/0.47  # Unit Clause-clause subsumption calls : 277
% 0.20/0.47  # Rewrite failures with RHS unbound    : 48
% 0.20/0.47  # BW rewrite match attempts            : 100
% 0.20/0.47  # BW rewrite match successes           : 26
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 74514
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.121 s
% 0.20/0.47  # System time              : 0.006 s
% 0.20/0.47  # Total time               : 0.127 s
% 0.20/0.47  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
