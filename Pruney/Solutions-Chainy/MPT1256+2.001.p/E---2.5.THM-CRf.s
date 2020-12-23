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
% DateTime   : Thu Dec  3 11:11:09 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  163 (55856 expanded)
%              Number of clauses        :  118 (27523 expanded)
%              Number of leaves         :   22 (14134 expanded)
%              Depth                    :   37
%              Number of atoms          :  393 (151475 expanded)
%              Number of equality atoms :   91 (26118 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t35_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(t33_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t72_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

fof(t41_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(commutativity_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t71_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k2_tops_1(X1,k1_tops_1(X1,X2)),k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tops_1)).

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_23,plain,(
    ! [X45,X46] :
      ( ( ~ m1_subset_1(X45,k1_zfmisc_1(X46))
        | r1_tarski(X45,X46) )
      & ( ~ r1_tarski(X45,X46)
        | m1_subset_1(X45,k1_zfmisc_1(X46)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_26,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
      | ~ r1_tarski(X40,k3_subset_1(X39,X41))
      | r1_tarski(X41,k3_subset_1(X39,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | m1_subset_1(k3_subset_1(X14,X15),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k3_subset_1(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

fof(c_0_36,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r1_tarski(X31,X32)
        | r1_tarski(k3_subset_1(X30,X32),k3_subset_1(X30,X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(X30)) )
      & ( ~ r1_tarski(k3_subset_1(X30,X32),k3_subset_1(X30,X31))
        | r1_tarski(X31,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_37,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,k3_subset_1(X2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = X1
    | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

fof(c_0_42,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | m1_subset_1(k9_subset_1(X16,X17,X18),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_43,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X27))
      | k9_subset_1(X27,X28,X29) = k3_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_39])])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_32])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k3_subset_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_41])).

cnf(c_0_52,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_xboole_0(X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_49])).

cnf(c_0_53,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k3_subset_1(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_39])])).

cnf(c_0_55,plain,
    ( k3_subset_1(X1,X1) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,X1)))
    | ~ m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_25])).

fof(c_0_57,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | ~ m1_subset_1(X35,k1_zfmisc_1(X33))
      | k7_subset_1(X33,X34,X35) = k9_subset_1(X33,X34,k3_subset_1(X33,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k3_subset_1(X2,X2)) = k3_subset_1(X2,X2)
    | ~ m1_subset_1(k3_xboole_0(X1,k3_subset_1(X2,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_39])).

cnf(c_0_59,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_56]),c_0_32])).

cnf(c_0_60,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k3_subset_1(X2,X2)) = k3_subset_1(X2,X2)
    | ~ m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_49])).

cnf(c_0_62,plain,
    ( k3_subset_1(X1,k3_subset_1(X2,X2)) = X1
    | ~ m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_53])).

fof(c_0_63,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | ~ m1_subset_1(X38,k1_zfmisc_1(X36))
      | k3_subset_1(X36,k7_subset_1(X36,X37,X38)) = k4_subset_1(X36,k3_subset_1(X36,X37),X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k3_subset_1(X2,X3)) = k7_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_60]),c_0_32])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k3_subset_1(X2,X2)) = k3_subset_1(X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_32]),c_0_39])])).

cnf(c_0_66,plain,
    ( k3_subset_1(X1,k3_subset_1(X2,X2)) = X1
    | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_53])).

fof(c_0_67,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k7_subset_1(X24,X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_68,plain,
    ( k3_subset_1(X2,k7_subset_1(X2,X1,X3)) = k4_subset_1(X2,k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( k7_subset_1(X1,X2,X1) = k3_subset_1(X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_39])])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_32]),c_0_39])])).

cnf(c_0_71,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X2),X1) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_39])])).

cnf(c_0_73,plain,
    ( k3_subset_1(X1,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_69])).

cnf(c_0_74,plain,
    ( m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_60]),c_0_32])).

fof(c_0_75,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k3_subset_1(X19,k3_subset_1(X19,X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_76,plain,
    ( k4_subset_1(X1,k4_xboole_0(X2,X1),X1) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_39])])).

cnf(c_0_77,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_69]),c_0_39])])).

cnf(c_0_78,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_79,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X1),X1) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_73])).

cnf(c_0_80,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_39])).

fof(c_0_81,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | k9_subset_1(X9,X10,X11) = k9_subset_1(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_82,plain,
    ( k3_subset_1(X1,k4_subset_1(X1,k3_subset_1(X1,X2),X3)) = k7_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_68]),c_0_74])).

cnf(c_0_83,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X1),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_85,plain,
    ( k7_subset_1(X1,X1,X1) = k3_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_39])])).

cnf(c_0_86,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_87,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_84])).

fof(c_0_88,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t72_tops_1])).

cnf(c_0_89,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_71])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_85]),c_0_39])])).

cnf(c_0_91,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

fof(c_0_92,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_tops_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_88])])])).

fof(c_0_93,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | r1_tarski(k3_subset_1(X42,k4_subset_1(X42,X43,X44)),k3_subset_1(X42,X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).

cnf(c_0_94,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_95,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_39])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_97,plain,
    ( r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,plain,
    ( k3_subset_1(X1,X1) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_50])).

cnf(c_0_99,plain,
    ( k3_subset_1(X1,k3_subset_1(X2,X2)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(esk2_0,X1),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_101,plain,
    ( r1_tarski(k3_subset_1(X1,k4_subset_1(X1,k3_subset_1(X1,X2),X3)),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_78]),c_0_32])).

cnf(c_0_102,plain,
    ( k3_subset_1(X1,X1) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_80])])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_65])).

cnf(c_0_104,plain,
    ( r1_tarski(k7_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_82])).

cnf(c_0_105,plain,
    ( k3_subset_1(X1,X1) = k3_subset_1(X2,X2)
    | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_53])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_32]),c_0_39])])).

cnf(c_0_107,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_71])).

cnf(c_0_108,plain,
    ( k4_subset_1(X1,X2,X1) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_78]),c_0_32])).

cnf(c_0_109,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_87])).

cnf(c_0_110,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)) = k3_subset_1(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

fof(c_0_111,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ m1_subset_1(X23,k1_zfmisc_1(X21))
      | k4_subset_1(X21,X22,X23) = k2_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_112,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | k4_subset_1(X6,X7,X8) = k4_subset_1(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).

cnf(c_0_113,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_39])).

cnf(c_0_114,plain,
    ( r1_tarski(k3_subset_1(X1,X1),k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_108]),c_0_39])])).

cnf(c_0_115,plain,
    ( k3_xboole_0(k3_subset_1(X1,X1),X2) = k3_subset_1(X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_94]),c_0_65])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_110]),c_0_39])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_96])).

cnf(c_0_118,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_119,plain,
    ( k4_subset_1(X2,X1,X3) = k4_subset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_120,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_113])).

cnf(c_0_121,plain,
    ( r1_tarski(k3_subset_1(X1,X1),k4_xboole_0(X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_73]),c_0_39])])).

cnf(c_0_122,negated_conjecture,
    ( k3_subset_1(esk2_0,esk2_0) = k3_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_65])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(X1,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_117])).

cnf(c_0_124,plain,
    ( k4_subset_1(X1,X2,X3) = k2_xboole_0(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_125,plain,
    ( k4_xboole_0(k3_subset_1(X1,X1),X1) = k3_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_80])])).

cnf(c_0_126,negated_conjecture,
    ( k3_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k4_xboole_0(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_39])])).

fof(c_0_127,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,X13) = k4_xboole_0(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_110])).

cnf(c_0_129,plain,
    ( k2_xboole_0(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_83]),c_0_80]),c_0_39])])).

cnf(c_0_130,negated_conjecture,
    ( k4_xboole_0(k3_subset_1(esk2_0,esk2_0),k4_xboole_0(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_131,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_127])).

cnf(c_0_132,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_123]),c_0_39])])).

cnf(c_0_133,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_73])).

cnf(c_0_134,negated_conjecture,
    ( k4_xboole_0(k3_subset_1(esk2_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_96])])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_131]),c_0_96])])).

cnf(c_0_136,plain,
    ( k3_subset_1(X1,k2_xboole_0(k3_subset_1(X1,X2),X3)) = k7_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_118]),c_0_32])).

cnf(c_0_137,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(esk2_0,esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_135])])).

cnf(c_0_138,plain,
    ( m1_subset_1(k4_subset_1(X1,k3_subset_1(X1,X2),X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_68]),c_0_74])).

fof(c_0_139,plain,(
    ! [X53,X54] :
      ( ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | k2_pre_topc(X53,X54) = k4_subset_1(u1_struct_0(X53),X54,k2_tops_1(X53,X54)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_140,plain,(
    ! [X51,X52] :
      ( ~ l1_pre_topc(X51)
      | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
      | k2_tops_1(X51,X52) = k2_tops_1(X51,k3_subset_1(u1_struct_0(X51),X52)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_141,plain,(
    ! [X47,X48] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
      | k1_tops_1(X47,X48) = k3_subset_1(u1_struct_0(X47),k2_pre_topc(X47,k3_subset_1(u1_struct_0(X47),X48))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_142,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_71])).

cnf(c_0_143,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(esk2_0,esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_116]),c_0_96])])).

cnf(c_0_144,plain,
    ( m1_subset_1(k2_xboole_0(k3_subset_1(X1,X2),X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_118]),c_0_32])).

cnf(c_0_145,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_139])).

cnf(c_0_146,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_140])).

fof(c_0_147,plain,(
    ! [X49,X50] :
      ( ~ l1_pre_topc(X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
      | m1_subset_1(k2_tops_1(X49,X50),k1_zfmisc_1(u1_struct_0(X49))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_148,plain,(
    ! [X55,X56] :
      ( ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | r1_tarski(k2_tops_1(X55,k1_tops_1(X55,X56)),k2_tops_1(X55,X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t71_tops_1])])])).

cnf(c_0_149,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_141])).

cnf(c_0_150,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_70]),c_0_80]),c_0_96])])).

cnf(c_0_151,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_152,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_137]),c_0_116]),c_0_96])])).

cnf(c_0_153,plain,
    ( k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2)) = k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_32])).

cnf(c_0_154,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_147])).

cnf(c_0_155,plain,
    ( r1_tarski(k2_tops_1(X1,k1_tops_1(X1,X2)),k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_148])).

cnf(c_0_156,negated_conjecture,
    ( k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_151]),c_0_152])])).

cnf(c_0_157,negated_conjecture,
    ( k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_150]),c_0_151]),c_0_152])])).

cnf(c_0_158,plain,
    ( m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_153]),c_0_154])).

cnf(c_0_159,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))),k2_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_156]),c_0_157]),c_0_151]),c_0_152])])).

cnf(c_0_160,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_150]),c_0_151]),c_0_152])])).

cnf(c_0_161,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_162,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_146]),c_0_151]),c_0_160])]),c_0_161]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:41:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.84/3.03  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.84/3.03  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.84/3.03  #
% 2.84/3.03  # Preprocessing time       : 0.028 s
% 2.84/3.03  # Presaturation interreduction done
% 2.84/3.03  
% 2.84/3.03  # Proof found!
% 2.84/3.03  # SZS status Theorem
% 2.84/3.03  # SZS output start CNFRefutation
% 2.84/3.03  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/3.03  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.84/3.03  fof(t35_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.84/3.03  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.84/3.03  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.84/3.03  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.84/3.03  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.84/3.03  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 2.84/3.03  fof(t33_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 2.84/3.03  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.84/3.03  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.84/3.03  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.84/3.03  fof(t72_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 2.84/3.03  fof(t41_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 2.84/3.03  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.84/3.03  fof(commutativity_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k4_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.84/3.03  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.84/3.03  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 2.84/3.03  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 2.84/3.03  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.84/3.03  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.84/3.03  fof(t71_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k2_tops_1(X1,k1_tops_1(X1,X2)),k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_tops_1)).
% 2.84/3.03  fof(c_0_22, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.84/3.03  fof(c_0_23, plain, ![X45, X46]:((~m1_subset_1(X45,k1_zfmisc_1(X46))|r1_tarski(X45,X46))&(~r1_tarski(X45,X46)|m1_subset_1(X45,k1_zfmisc_1(X46)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.84/3.03  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.84/3.03  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.84/3.03  fof(c_0_26, plain, ![X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|(~m1_subset_1(X41,k1_zfmisc_1(X39))|(~r1_tarski(X40,k3_subset_1(X39,X41))|r1_tarski(X41,k3_subset_1(X39,X40))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).
% 2.84/3.03  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.84/3.03  fof(c_0_28, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|m1_subset_1(k3_subset_1(X14,X15),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 2.84/3.03  cnf(c_0_29, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.84/3.03  cnf(c_0_30, plain, (r1_tarski(X3,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.84/3.03  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 2.84/3.03  cnf(c_0_32, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.84/3.03  cnf(c_0_33, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 2.84/3.03  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.84/3.03  cnf(c_0_35, plain, (r1_tarski(X1,k3_subset_1(X2,k3_subset_1(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 2.84/3.03  fof(c_0_36, plain, ![X30, X31, X32]:((~r1_tarski(X31,X32)|r1_tarski(k3_subset_1(X30,X32),k3_subset_1(X30,X31))|~m1_subset_1(X32,k1_zfmisc_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(X30)))&(~r1_tarski(k3_subset_1(X30,X32),k3_subset_1(X30,X31))|r1_tarski(X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(X30))|~m1_subset_1(X31,k1_zfmisc_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 2.84/3.03  cnf(c_0_37, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 2.84/3.03  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,k3_subset_1(X2,X1))))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 2.84/3.03  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 2.84/3.03  cnf(c_0_40, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.84/3.03  cnf(c_0_41, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=X1|~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 2.84/3.03  fof(c_0_42, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X16))|m1_subset_1(k9_subset_1(X16,X17,X18),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 2.84/3.03  fof(c_0_43, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(X27))|k9_subset_1(X27,X28,X29)=k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 2.84/3.03  cnf(c_0_44, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 2.84/3.03  cnf(c_0_45, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.84/3.03  cnf(c_0_46, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.84/3.03  cnf(c_0_47, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32]), c_0_39])])).
% 2.84/3.03  cnf(c_0_48, plain, (r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.84/3.03  cnf(c_0_49, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 2.84/3.03  cnf(c_0_50, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_25]), c_0_32])).
% 2.84/3.03  cnf(c_0_51, plain, (r1_tarski(X1,k3_subset_1(X1,X2))|~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,k3_subset_1(X1,X1))), inference(spm,[status(thm)],[c_0_48, c_0_41])).
% 2.84/3.03  cnf(c_0_52, plain, (X1=k3_xboole_0(X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k3_xboole_0(X2,X3)))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_49])).
% 2.84/3.03  cnf(c_0_53, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 2.84/3.03  cnf(c_0_54, plain, (r1_tarski(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,k3_subset_1(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_32]), c_0_39])])).
% 2.84/3.03  cnf(c_0_55, plain, (k3_subset_1(X1,X1)=k3_xboole_0(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,X1)))|~m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 2.84/3.03  cnf(c_0_56, plain, (r1_tarski(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_25])).
% 2.84/3.03  fof(c_0_57, plain, ![X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|(~m1_subset_1(X35,k1_zfmisc_1(X33))|k7_subset_1(X33,X34,X35)=k9_subset_1(X33,X34,k3_subset_1(X33,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 2.84/3.03  cnf(c_0_58, plain, (k3_xboole_0(X1,k3_subset_1(X2,X2))=k3_subset_1(X2,X2)|~m1_subset_1(k3_xboole_0(X1,k3_subset_1(X2,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_55, c_0_39])).
% 2.84/3.03  cnf(c_0_59, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_56]), c_0_32])).
% 2.84/3.03  cnf(c_0_60, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 2.84/3.03  cnf(c_0_61, plain, (k3_xboole_0(X1,k3_subset_1(X2,X2))=k3_subset_1(X2,X2)|~m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_58, c_0_49])).
% 2.84/3.03  cnf(c_0_62, plain, (k3_subset_1(X1,k3_subset_1(X2,X2))=X1|~m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1))|~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_59, c_0_53])).
% 2.84/3.03  fof(c_0_63, plain, ![X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|(~m1_subset_1(X38,k1_zfmisc_1(X36))|k3_subset_1(X36,k7_subset_1(X36,X37,X38))=k4_subset_1(X36,k3_subset_1(X36,X37),X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).
% 2.84/3.03  cnf(c_0_64, plain, (k3_xboole_0(X1,k3_subset_1(X2,X3))=k7_subset_1(X2,X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_60]), c_0_32])).
% 2.84/3.03  cnf(c_0_65, plain, (k3_xboole_0(X1,k3_subset_1(X2,X2))=k3_subset_1(X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_32]), c_0_39])])).
% 2.84/3.03  cnf(c_0_66, plain, (k3_subset_1(X1,k3_subset_1(X2,X2))=X1|~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_62, c_0_53])).
% 2.84/3.03  fof(c_0_67, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k7_subset_1(X24,X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 2.84/3.03  cnf(c_0_68, plain, (k3_subset_1(X2,k7_subset_1(X2,X1,X3))=k4_subset_1(X2,k3_subset_1(X2,X1),X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.84/3.03  cnf(c_0_69, plain, (k7_subset_1(X1,X2,X1)=k3_subset_1(X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_39])])).
% 2.84/3.03  cnf(c_0_70, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_32]), c_0_39])])).
% 2.84/3.03  cnf(c_0_71, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 2.84/3.03  cnf(c_0_72, plain, (k4_subset_1(X1,k3_subset_1(X1,X2),X1)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_39])])).
% 2.84/3.03  cnf(c_0_73, plain, (k3_subset_1(X1,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_69])).
% 2.84/3.03  cnf(c_0_74, plain, (m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_60]), c_0_32])).
% 2.84/3.03  fof(c_0_75, plain, ![X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|k3_subset_1(X19,k3_subset_1(X19,X20))=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 2.84/3.03  cnf(c_0_76, plain, (k4_subset_1(X1,k4_xboole_0(X2,X1),X1)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_39])])).
% 2.84/3.03  cnf(c_0_77, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_69]), c_0_39])])).
% 2.84/3.03  cnf(c_0_78, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 2.84/3.03  cnf(c_0_79, plain, (k4_subset_1(X1,k3_subset_1(X1,X1),X1)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_76, c_0_73])).
% 2.84/3.03  cnf(c_0_80, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_77, c_0_39])).
% 2.84/3.03  fof(c_0_81, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|k9_subset_1(X9,X10,X11)=k9_subset_1(X9,X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 2.84/3.03  cnf(c_0_82, plain, (k3_subset_1(X1,k4_subset_1(X1,k3_subset_1(X1,X2),X3))=k7_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_68]), c_0_74])).
% 2.84/3.03  cnf(c_0_83, plain, (k4_subset_1(X1,k3_subset_1(X1,X1),X1)=X1), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 2.84/3.03  cnf(c_0_84, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 2.84/3.03  cnf(c_0_85, plain, (k7_subset_1(X1,X1,X1)=k3_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_39])])).
% 2.84/3.03  cnf(c_0_86, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_46])).
% 2.84/3.03  cnf(c_0_87, plain, (k9_subset_1(X1,X2,X3)=k3_xboole_0(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_46, c_0_84])).
% 2.84/3.03  fof(c_0_88, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2))))), inference(assume_negation,[status(cth)],[t72_tops_1])).
% 2.84/3.03  cnf(c_0_89, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_74, c_0_71])).
% 2.84/3.03  cnf(c_0_90, plain, (k4_xboole_0(X1,X1)=k3_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_85]), c_0_39])])).
% 2.84/3.03  cnf(c_0_91, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 2.84/3.03  fof(c_0_92, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_tops_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_88])])])).
% 2.84/3.03  fof(c_0_93, plain, ![X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|(~m1_subset_1(X44,k1_zfmisc_1(X42))|r1_tarski(k3_subset_1(X42,k4_subset_1(X42,X43,X44)),k3_subset_1(X42,X43)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).
% 2.84/3.03  cnf(c_0_94, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 2.84/3.03  cnf(c_0_95, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_91, c_0_39])).
% 2.84/3.03  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 2.84/3.03  cnf(c_0_97, plain, (r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 2.84/3.03  cnf(c_0_98, plain, (k3_subset_1(X1,X1)=X2|~m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_50])).
% 2.84/3.03  cnf(c_0_99, plain, (k3_subset_1(X1,k3_subset_1(X2,X2))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_66, c_0_94])).
% 2.84/3.03  cnf(c_0_100, negated_conjecture, (m1_subset_1(k3_xboole_0(esk2_0,X1),k1_zfmisc_1(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 2.84/3.03  cnf(c_0_101, plain, (r1_tarski(k3_subset_1(X1,k4_subset_1(X1,k3_subset_1(X1,X2),X3)),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_78]), c_0_32])).
% 2.84/3.03  cnf(c_0_102, plain, (k3_subset_1(X1,X1)=X2|~m1_subset_1(X2,k1_zfmisc_1(k3_subset_1(X1,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_80])])).
% 2.84/3.03  cnf(c_0_103, negated_conjecture, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(esk2_0))|~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_100, c_0_65])).
% 2.84/3.03  cnf(c_0_104, plain, (r1_tarski(k7_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_101, c_0_82])).
% 2.84/3.03  cnf(c_0_105, plain, (k3_subset_1(X1,X1)=k3_subset_1(X2,X2)|~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_102, c_0_53])).
% 2.84/3.03  cnf(c_0_106, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_32]), c_0_39])])).
% 2.84/3.03  cnf(c_0_107, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_104, c_0_71])).
% 2.84/3.03  cnf(c_0_108, plain, (k4_subset_1(X1,X2,X1)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_78]), c_0_32])).
% 2.84/3.03  cnf(c_0_109, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_46, c_0_87])).
% 2.84/3.03  cnf(c_0_110, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))=k3_subset_1(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 2.84/3.03  fof(c_0_111, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|~m1_subset_1(X23,k1_zfmisc_1(X21))|k4_subset_1(X21,X22,X23)=k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 2.84/3.03  fof(c_0_112, plain, ![X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(X6))|~m1_subset_1(X8,k1_zfmisc_1(X6))|k4_subset_1(X6,X7,X8)=k4_subset_1(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).
% 2.84/3.03  cnf(c_0_113, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_107, c_0_39])).
% 2.84/3.03  cnf(c_0_114, plain, (r1_tarski(k3_subset_1(X1,X1),k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_108]), c_0_39])])).
% 2.84/3.03  cnf(c_0_115, plain, (k3_xboole_0(k3_subset_1(X1,X1),X2)=k3_subset_1(X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_94]), c_0_65])).
% 2.84/3.03  cnf(c_0_116, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_110]), c_0_39])])).
% 2.84/3.03  cnf(c_0_117, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk2_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_107, c_0_96])).
% 2.84/3.03  cnf(c_0_118, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 2.84/3.03  cnf(c_0_119, plain, (k4_subset_1(X2,X1,X3)=k4_subset_1(X2,X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 2.84/3.03  cnf(c_0_120, plain, (k4_xboole_0(X1,X2)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_24, c_0_113])).
% 2.84/3.03  cnf(c_0_121, plain, (r1_tarski(k3_subset_1(X1,X1),k4_xboole_0(X2,X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_73]), c_0_39])])).
% 2.84/3.03  cnf(c_0_122, negated_conjecture, (k3_subset_1(esk2_0,esk2_0)=k3_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_65])).
% 2.84/3.03  cnf(c_0_123, negated_conjecture, (m1_subset_1(k4_xboole_0(X1,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_34, c_0_117])).
% 2.84/3.03  cnf(c_0_124, plain, (k4_subset_1(X1,X2,X3)=k2_xboole_0(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 2.84/3.03  cnf(c_0_125, plain, (k4_xboole_0(k3_subset_1(X1,X1),X1)=k3_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_80])])).
% 2.84/3.03  cnf(c_0_126, negated_conjecture, (k3_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k4_xboole_0(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_39])])).
% 2.84/3.03  fof(c_0_127, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,X13)=k4_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 2.84/3.03  cnf(c_0_128, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_53, c_0_110])).
% 2.84/3.03  cnf(c_0_129, plain, (k2_xboole_0(X1,k3_subset_1(X1,X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_83]), c_0_80]), c_0_39])])).
% 2.84/3.03  cnf(c_0_130, negated_conjecture, (k4_xboole_0(k3_subset_1(esk2_0,esk2_0),k4_xboole_0(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 2.84/3.03  cnf(c_0_131, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_127])).
% 2.84/3.03  cnf(c_0_132, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_123]), c_0_39])])).
% 2.84/3.03  cnf(c_0_133, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_129, c_0_73])).
% 2.84/3.03  cnf(c_0_134, negated_conjecture, (k4_xboole_0(k3_subset_1(esk2_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_96])])).
% 2.84/3.03  cnf(c_0_135, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_131]), c_0_96])])).
% 2.84/3.03  cnf(c_0_136, plain, (k3_subset_1(X1,k2_xboole_0(k3_subset_1(X1,X2),X3))=k7_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_118]), c_0_32])).
% 2.84/3.03  cnf(c_0_137, negated_conjecture, (k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(esk2_0,esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_135])])).
% 2.84/3.03  cnf(c_0_138, plain, (m1_subset_1(k4_subset_1(X1,k3_subset_1(X1,X2),X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_68]), c_0_74])).
% 2.84/3.03  fof(c_0_139, plain, ![X53, X54]:(~l1_pre_topc(X53)|(~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|k2_pre_topc(X53,X54)=k4_subset_1(u1_struct_0(X53),X54,k2_tops_1(X53,X54)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 2.84/3.03  fof(c_0_140, plain, ![X51, X52]:(~l1_pre_topc(X51)|(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))|k2_tops_1(X51,X52)=k2_tops_1(X51,k3_subset_1(u1_struct_0(X51),X52)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 2.84/3.03  fof(c_0_141, plain, ![X47, X48]:(~l1_pre_topc(X47)|(~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|k1_tops_1(X47,X48)=k3_subset_1(u1_struct_0(X47),k2_pre_topc(X47,k3_subset_1(u1_struct_0(X47),X48))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 2.84/3.03  cnf(c_0_142, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_131, c_0_71])).
% 2.84/3.03  cnf(c_0_143, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(esk2_0,esk2_0))=k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_116]), c_0_96])])).
% 2.84/3.03  cnf(c_0_144, plain, (m1_subset_1(k2_xboole_0(k3_subset_1(X1,X2),X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_118]), c_0_32])).
% 2.84/3.03  cnf(c_0_145, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_139])).
% 2.84/3.03  cnf(c_0_146, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_140])).
% 2.84/3.03  fof(c_0_147, plain, ![X49, X50]:(~l1_pre_topc(X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|m1_subset_1(k2_tops_1(X49,X50),k1_zfmisc_1(u1_struct_0(X49)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 2.84/3.03  fof(c_0_148, plain, ![X55, X56]:(~l1_pre_topc(X55)|(~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|r1_tarski(k2_tops_1(X55,k1_tops_1(X55,X56)),k2_tops_1(X55,X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t71_tops_1])])])).
% 2.84/3.03  cnf(c_0_149, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_141])).
% 2.84/3.03  cnf(c_0_150, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_70]), c_0_80]), c_0_96])])).
% 2.84/3.03  cnf(c_0_151, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 2.84/3.03  cnf(c_0_152, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_137]), c_0_116]), c_0_96])])).
% 2.84/3.03  cnf(c_0_153, plain, (k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2))=k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_32])).
% 2.84/3.03  cnf(c_0_154, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_147])).
% 2.84/3.03  cnf(c_0_155, plain, (r1_tarski(k2_tops_1(X1,k1_tops_1(X1,X2)),k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_148])).
% 2.84/3.03  cnf(c_0_156, negated_conjecture, (k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_151]), c_0_152])])).
% 2.84/3.03  cnf(c_0_157, negated_conjecture, (k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_150]), c_0_151]), c_0_152])])).
% 2.84/3.03  cnf(c_0_158, plain, (m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_153]), c_0_154])).
% 2.84/3.03  cnf(c_0_159, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))),k2_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_156]), c_0_157]), c_0_151]), c_0_152])])).
% 2.84/3.03  cnf(c_0_160, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_150]), c_0_151]), c_0_152])])).
% 2.84/3.03  cnf(c_0_161, negated_conjecture, (~r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 2.84/3.03  cnf(c_0_162, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_146]), c_0_151]), c_0_160])]), c_0_161]), ['proof']).
% 2.84/3.03  # SZS output end CNFRefutation
% 2.84/3.03  # Proof object total steps             : 163
% 2.84/3.03  # Proof object clause steps            : 118
% 2.84/3.03  # Proof object formula steps           : 45
% 2.84/3.03  # Proof object conjectures             : 29
% 2.84/3.03  # Proof object clause conjectures      : 26
% 2.84/3.03  # Proof object formula conjectures     : 3
% 2.84/3.03  # Proof object initial clauses used    : 27
% 2.84/3.03  # Proof object initial formulas used   : 22
% 2.84/3.03  # Proof object generating inferences   : 90
% 2.84/3.03  # Proof object simplifying inferences  : 91
% 2.84/3.03  # Training examples: 0 positive, 0 negative
% 2.84/3.03  # Parsed axioms                        : 22
% 2.84/3.03  # Removed by relevancy pruning/SinE    : 0
% 2.84/3.03  # Initial clauses                      : 28
% 2.84/3.03  # Removed in clause preprocessing      : 0
% 2.84/3.03  # Initial clauses in saturation        : 28
% 2.84/3.03  # Processed clauses                    : 20253
% 2.84/3.03  # ...of these trivial                  : 210
% 2.84/3.03  # ...subsumed                          : 16862
% 2.84/3.03  # ...remaining for further processing  : 3181
% 2.84/3.03  # Other redundant clauses eliminated   : 2
% 2.84/3.03  # Clauses deleted for lack of memory   : 0
% 2.84/3.03  # Backward-subsumed                    : 508
% 2.84/3.03  # Backward-rewritten                   : 489
% 2.84/3.03  # Generated clauses                    : 226501
% 2.84/3.03  # ...of the previous two non-trivial   : 217125
% 2.84/3.03  # Contextual simplify-reflections      : 396
% 2.84/3.03  # Paramodulations                      : 226499
% 2.84/3.03  # Factorizations                       : 0
% 2.84/3.03  # Equation resolutions                 : 2
% 2.84/3.03  # Propositional unsat checks           : 0
% 2.84/3.03  #    Propositional check models        : 0
% 2.84/3.03  #    Propositional check unsatisfiable : 0
% 2.84/3.03  #    Propositional clauses             : 0
% 2.84/3.03  #    Propositional clauses after purity: 0
% 2.84/3.03  #    Propositional unsat core size     : 0
% 2.84/3.03  #    Propositional preprocessing time  : 0.000
% 2.84/3.03  #    Propositional encoding time       : 0.000
% 2.84/3.03  #    Propositional solver time         : 0.000
% 2.84/3.03  #    Success case prop preproc time    : 0.000
% 2.84/3.03  #    Success case prop encoding time   : 0.000
% 2.84/3.03  #    Success case prop solver time     : 0.000
% 2.84/3.03  # Current number of processed clauses  : 2155
% 2.84/3.03  #    Positive orientable unit clauses  : 134
% 2.84/3.03  #    Positive unorientable unit clauses: 0
% 2.84/3.03  #    Negative unit clauses             : 21
% 2.84/3.03  #    Non-unit-clauses                  : 2000
% 2.84/3.03  # Current number of unprocessed clauses: 195171
% 2.84/3.03  # ...number of literals in the above   : 974929
% 2.84/3.03  # Current number of archived formulas  : 0
% 2.84/3.03  # Current number of archived clauses   : 1024
% 2.84/3.03  # Clause-clause subsumption calls (NU) : 1628051
% 2.84/3.03  # Rec. Clause-clause subsumption calls : 565309
% 2.84/3.03  # Non-unit clause-clause subsumptions  : 12205
% 2.84/3.03  # Unit Clause-clause subsumption calls : 26473
% 2.84/3.03  # Rewrite failures with RHS unbound    : 0
% 2.84/3.03  # BW rewrite match attempts            : 261
% 2.84/3.03  # BW rewrite match successes           : 60
% 2.84/3.03  # Condensation attempts                : 0
% 2.84/3.03  # Condensation successes               : 0
% 2.84/3.03  # Termbank termtop insertions          : 5482642
% 2.84/3.04  
% 2.84/3.04  # -------------------------------------------------
% 2.84/3.04  # User time                : 2.603 s
% 2.84/3.04  # System time              : 0.101 s
% 2.84/3.04  # Total time               : 2.704 s
% 2.84/3.04  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
