%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:54 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 (2550 expanded)
%              Number of clauses        :   97 (1097 expanded)
%              Number of leaves         :   24 ( 651 expanded)
%              Depth                    :   16
%              Number of atoms          :  505 (12895 expanded)
%              Number of equality atoms :  104 (2432 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   76 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

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

fof(t80_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( X3 != k1_xboole_0
                    & v3_pre_topc(X3,X1)
                    & r1_xboole_0(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(d13_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k2_pre_topc(X1,X2)
              <=> ! [X4] :
                    ( r2_hidden(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v3_pre_topc(X5,X1)
                              & r2_hidden(X4,X5)
                              & r1_xboole_0(X2,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

fof(t54_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ( ~ v2_struct_0(X1)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ~ ( v3_pre_topc(X4,X1)
                          & r2_hidden(X3,X4)
                          & r1_xboole_0(X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(t27_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(c_0_24,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_25,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_26,plain,(
    ! [X19] : m1_subset_1(k2_subset_1(X19),k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_27,plain,(
    ! [X16] : k2_subset_1(X16) = X16 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_28,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X12] : k3_xboole_0(X12,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_32,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k3_xboole_0(X10,X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_33,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_43,plain,(
    ! [X40] :
      ( ~ l1_struct_0(X40)
      | k2_struct_0(X40) = u1_struct_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_44,plain,(
    ! [X41] :
      ( ~ l1_pre_topc(X41)
      | l1_struct_0(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v1_tops_1(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ~ ( X3 != k1_xboole_0
                      & v3_pre_topc(X3,X1)
                      & r1_xboole_0(X2,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t80_tops_1])).

fof(c_0_46,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k3_subset_1(X17,X18) = k4_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_54,negated_conjecture,(
    ! [X58] :
      ( v2_pre_topc(esk5_0)
      & l1_pre_topc(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | ~ v1_tops_1(esk6_0,esk5_0) )
      & ( esk7_0 != k1_xboole_0
        | ~ v1_tops_1(esk6_0,esk5_0) )
      & ( v3_pre_topc(esk7_0,esk5_0)
        | ~ v1_tops_1(esk6_0,esk5_0) )
      & ( r1_xboole_0(esk6_0,esk7_0)
        | ~ v1_tops_1(esk6_0,esk5_0) )
      & ( v1_tops_1(esk6_0,esk5_0)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | X58 = k1_xboole_0
        | ~ v3_pre_topc(X58,esk5_0)
        | ~ r1_xboole_0(esk6_0,X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])])])).

fof(c_0_55,plain,(
    ! [X31,X32,X33,X34,X35,X39] :
      ( ( ~ r2_hidden(X34,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v3_pre_topc(X35,X31)
        | ~ r2_hidden(X34,X35)
        | ~ r1_xboole_0(X32,X35)
        | ~ r2_hidden(X34,u1_struct_0(X31))
        | X33 != k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk1_4(X31,X32,X33,X34),k1_zfmisc_1(u1_struct_0(X31)))
        | r2_hidden(X34,X33)
        | ~ r2_hidden(X34,u1_struct_0(X31))
        | X33 != k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( v3_pre_topc(esk1_4(X31,X32,X33,X34),X31)
        | r2_hidden(X34,X33)
        | ~ r2_hidden(X34,u1_struct_0(X31))
        | X33 != k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(X34,esk1_4(X31,X32,X33,X34))
        | r2_hidden(X34,X33)
        | ~ r2_hidden(X34,u1_struct_0(X31))
        | X33 != k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( r1_xboole_0(X32,esk1_4(X31,X32,X33,X34))
        | r2_hidden(X34,X33)
        | ~ r2_hidden(X34,u1_struct_0(X31))
        | X33 != k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk2_3(X31,X32,X33),u1_struct_0(X31))
        | X33 = k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk3_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ r2_hidden(esk2_3(X31,X32,X33),X33)
        | X33 = k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( v3_pre_topc(esk3_3(X31,X32,X33),X31)
        | ~ r2_hidden(esk2_3(X31,X32,X33),X33)
        | X33 = k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk2_3(X31,X32,X33),esk3_3(X31,X32,X33))
        | ~ r2_hidden(esk2_3(X31,X32,X33),X33)
        | X33 = k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( r1_xboole_0(X32,esk3_3(X31,X32,X33))
        | ~ r2_hidden(esk2_3(X31,X32,X33),X33)
        | X33 = k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk2_3(X31,X32,X33),X33)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v3_pre_topc(X39,X31)
        | ~ r2_hidden(esk2_3(X31,X32,X33),X39)
        | ~ r1_xboole_0(X32,X39)
        | X33 = k2_pre_topc(X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).

fof(c_0_56,plain,(
    ! [X44,X45,X46,X47] :
      ( ( ~ v2_struct_0(X44)
        | ~ r2_hidden(X46,k2_pre_topc(X44,X45))
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) )
      & ( ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ v3_pre_topc(X47,X44)
        | ~ r2_hidden(X46,X47)
        | ~ r1_xboole_0(X45,X47)
        | ~ r2_hidden(X46,k2_pre_topc(X44,X45))
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) )
      & ( m1_subset_1(esk4_3(X44,X45,X46),k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | r2_hidden(X46,k2_pre_topc(X44,X45))
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) )
      & ( v3_pre_topc(esk4_3(X44,X45,X46),X44)
        | v2_struct_0(X44)
        | r2_hidden(X46,k2_pre_topc(X44,X45))
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) )
      & ( r2_hidden(X46,esk4_3(X44,X45,X46))
        | v2_struct_0(X44)
        | r2_hidden(X46,k2_pre_topc(X44,X45))
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) )
      & ( r1_xboole_0(X45,esk4_3(X44,X45,X46))
        | v2_struct_0(X44)
        | r2_hidden(X46,k2_pre_topc(X44,X45))
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).

fof(c_0_57,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | m1_subset_1(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_58,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_59,plain,(
    ! [X53,X54] :
      ( ( ~ v4_pre_topc(X54,X53)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X53),X54),X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
        | ~ l1_pre_topc(X53) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X53),X54),X53)
        | v4_pre_topc(X54,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
        | ~ l1_pre_topc(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_60,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_30]),c_0_38]),c_0_38])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_63,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_64,plain,(
    ! [X52] :
      ( ~ l1_pre_topc(X52)
      | k2_pre_topc(X52,k2_struct_0(X52)) = k2_struct_0(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).

cnf(c_0_65,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X4,X1)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_38])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_49]),c_0_62]),c_0_63])).

fof(c_0_74,plain,(
    ! [X42,X43] :
      ( ( ~ v4_pre_topc(X43,X42)
        | k2_pre_topc(X42,X43) = X43
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ l1_pre_topc(X42) )
      & ( ~ v2_pre_topc(X42)
        | k2_pre_topc(X42,X43) != X43
        | v4_pre_topc(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_75,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( k2_struct_0(esk5_0) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k2_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_78,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_42])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,esk3_3(X2,X1,X3))
    | X3 = k2_pre_topc(X2,X1)
    | ~ r2_hidden(esk2_3(X2,X1,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_80,plain,
    ( v3_pre_topc(esk3_3(X1,X2,X3),X1)
    | X3 = k2_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_81,plain,(
    ! [X49,X50] :
      ( ( ~ v1_tops_1(X50,X49)
        | k2_pre_topc(X49,X50) = k2_struct_0(X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ l1_pre_topc(X49) )
      & ( k2_pre_topc(X49,X50) != k2_struct_0(X49)
        | v1_tops_1(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

cnf(c_0_82,plain,
    ( ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X4))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_xboole_0(X4,X1) ),
    inference(csr,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_84,plain,(
    ! [X23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_85,plain,
    ( r1_xboole_0(X1,X2)
    | k1_setfam_1(k2_tarski(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_30])).

cnf(c_0_86,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)),X1)
    | ~ v4_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_42])).

cnf(c_0_87,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_42]),c_0_63]),c_0_73])).

cnf(c_0_88,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_89,negated_conjecture,
    ( k2_pre_topc(esk5_0,u1_struct_0(esk5_0)) = u1_struct_0(esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_66]),c_0_76]),c_0_76])).

cnf(c_0_90,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_91,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ r2_hidden(X22,X21)
      | r2_hidden(X22,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_92,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3))
    | X3 = k2_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_93,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | m1_subset_1(esk3_3(X1,X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_42]),c_0_78])).

cnf(c_0_94,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | r1_xboole_0(X2,esk3_3(X1,X2,u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_42]),c_0_78])).

cnf(c_0_95,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | v3_pre_topc(esk3_3(X1,X2,u1_struct_0(X1)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_42]),c_0_78])).

cnf(c_0_96,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_97,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,k2_pre_topc(esk5_0,esk6_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_66])])).

cnf(c_0_98,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_99,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_49])).

cnf(c_0_100,plain,
    ( v3_pre_topc(k1_xboole_0,X1)
    | ~ v4_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_101,negated_conjecture,
    ( v4_pre_topc(u1_struct_0(esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_66]),c_0_42])])).

cnf(c_0_102,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_103,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),esk3_3(X1,X2,u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_42]),c_0_78])).

cnf(c_0_104,negated_conjecture,
    ( v1_tops_1(esk6_0,esk5_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_105,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_83]),c_0_66])])).

cnf(c_0_106,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | r1_xboole_0(esk6_0,esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_83]),c_0_66])])).

cnf(c_0_107,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | v3_pre_topc(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_83]),c_0_66])])).

cnf(c_0_108,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_83]),c_0_76]),c_0_66])])).

cnf(c_0_109,negated_conjecture,
    ( ~ v3_pre_topc(k1_xboole_0,esk5_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])])).

cnf(c_0_110,negated_conjecture,
    ( v3_pre_topc(k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_66])])).

cnf(c_0_111,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_98])).

cnf(c_0_112,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_113,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | r2_hidden(esk2_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_83]),c_0_66])])).

cnf(c_0_114,negated_conjecture,
    ( esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)) = k1_xboole_0
    | k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106]),c_0_107]),c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110])]),c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( v1_tops_1(X1,esk5_0)
    | k2_pre_topc(esk5_0,X1) != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_76]),c_0_66])])).

cnf(c_0_117,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

fof(c_0_118,plain,(
    ! [X51] :
      ( ~ v2_pre_topc(X51)
      | ~ l1_pre_topc(X51)
      | v3_pre_topc(k2_struct_0(X51),X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_120,negated_conjecture,
    ( v1_tops_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_83])])).

cnf(c_0_121,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0)
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_122,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0)
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_123,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_124,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_98]),c_0_49]),c_0_62])).

cnf(c_0_125,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_126,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X4)
    | ~ r1_xboole_0(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_127,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_117]),c_0_102])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120])])).

cnf(c_0_129,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_120])])).

cnf(c_0_130,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_120])])).

cnf(c_0_131,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_132,plain,
    ( v4_pre_topc(k1_xboole_0,X1)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_98]),c_0_124])).

cnf(c_0_133,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_90]),c_0_76]),c_0_66])])).

cnf(c_0_134,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_98])).

cnf(c_0_135,plain,
    ( X1 = k2_pre_topc(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_xboole_0(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_42]),c_0_67])).

cnf(c_0_136,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129]),c_0_130])])).

cnf(c_0_137,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_131,c_0_98])).

cnf(c_0_138,negated_conjecture,
    ( v4_pre_topc(k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_66])])).

cnf(c_0_139,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_134])).

cnf(c_0_140,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_141,negated_conjecture,
    ( k2_pre_topc(esk5_0,X1) = esk7_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_128]),c_0_133]),c_0_66])]),c_0_136])).

cnf(c_0_142,negated_conjecture,
    ( k2_pre_topc(esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_66])])).

cnf(c_0_143,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_139])).

cnf(c_0_144,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_120])])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_98]),c_0_142]),c_0_143])]),c_0_144]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.45  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.053 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.45  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.45  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.45  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.45  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.45  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.45  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.45  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.45  fof(t80_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X3!=k1_xboole_0&v3_pre_topc(X3,X1))&r1_xboole_0(X2,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tops_1)).
% 0.20/0.45  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.45  fof(d13_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k2_pre_topc(X1,X2)<=>![X4]:(r2_hidden(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X5,X1)&r2_hidden(X4,X5))&r1_xboole_0(X2,X5)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_pre_topc)).
% 0.20/0.45  fof(t54_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>(~(v2_struct_0(X1))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_pre_topc)).
% 0.20/0.45  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.45  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.45  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 0.20/0.45  fof(t27_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 0.20/0.45  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.45  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 0.20/0.45  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.45  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.45  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.20/0.45  fof(c_0_24, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.45  fof(c_0_25, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.45  fof(c_0_26, plain, ![X19]:m1_subset_1(k2_subset_1(X19),k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.45  fof(c_0_27, plain, ![X16]:k2_subset_1(X16)=X16, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.45  fof(c_0_28, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.45  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_30, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  fof(c_0_31, plain, ![X12]:k3_xboole_0(X12,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.45  fof(c_0_32, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k3_xboole_0(X10,X11)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.45  fof(c_0_33, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.45  cnf(c_0_34, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.45  cnf(c_0_35, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.45  fof(c_0_36, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.45  cnf(c_0_37, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.45  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.45  cnf(c_0_39, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.45  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.45  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.45  fof(c_0_43, plain, ![X40]:(~l1_struct_0(X40)|k2_struct_0(X40)=u1_struct_0(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.45  fof(c_0_44, plain, ![X41]:(~l1_pre_topc(X41)|l1_struct_0(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.45  fof(c_0_45, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X3!=k1_xboole_0&v3_pre_topc(X3,X1))&r1_xboole_0(X2,X3)))))))), inference(assume_negation,[status(cth)],[t80_tops_1])).
% 0.20/0.45  fof(c_0_46, plain, ![X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|k3_subset_1(X17,X18)=k4_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.45  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.45  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.45  cnf(c_0_49, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_39, c_0_30])).
% 0.20/0.45  cnf(c_0_50, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_30])).
% 0.20/0.45  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.45  cnf(c_0_52, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.45  cnf(c_0_53, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  fof(c_0_54, negated_conjecture, ![X58]:((v2_pre_topc(esk5_0)&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(((m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_tops_1(esk6_0,esk5_0))&(((esk7_0!=k1_xboole_0|~v1_tops_1(esk6_0,esk5_0))&(v3_pre_topc(esk7_0,esk5_0)|~v1_tops_1(esk6_0,esk5_0)))&(r1_xboole_0(esk6_0,esk7_0)|~v1_tops_1(esk6_0,esk5_0))))&(v1_tops_1(esk6_0,esk5_0)|(~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(esk5_0)))|(X58=k1_xboole_0|~v3_pre_topc(X58,esk5_0)|~r1_xboole_0(esk6_0,X58))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])])])).
% 0.20/0.45  fof(c_0_55, plain, ![X31, X32, X33, X34, X35, X39]:(((~r2_hidden(X34,X33)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X31)))|(~v3_pre_topc(X35,X31)|~r2_hidden(X34,X35)|~r1_xboole_0(X32,X35)))|~r2_hidden(X34,u1_struct_0(X31))|X33!=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))&((m1_subset_1(esk1_4(X31,X32,X33,X34),k1_zfmisc_1(u1_struct_0(X31)))|r2_hidden(X34,X33)|~r2_hidden(X34,u1_struct_0(X31))|X33!=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))&(((v3_pre_topc(esk1_4(X31,X32,X33,X34),X31)|r2_hidden(X34,X33)|~r2_hidden(X34,u1_struct_0(X31))|X33!=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))&(r2_hidden(X34,esk1_4(X31,X32,X33,X34))|r2_hidden(X34,X33)|~r2_hidden(X34,u1_struct_0(X31))|X33!=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31)))&(r1_xboole_0(X32,esk1_4(X31,X32,X33,X34))|r2_hidden(X34,X33)|~r2_hidden(X34,u1_struct_0(X31))|X33!=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31)))))&((r2_hidden(esk2_3(X31,X32,X33),u1_struct_0(X31))|X33=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))&(((m1_subset_1(esk3_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))|~r2_hidden(esk2_3(X31,X32,X33),X33)|X33=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))&(((v3_pre_topc(esk3_3(X31,X32,X33),X31)|~r2_hidden(esk2_3(X31,X32,X33),X33)|X33=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))&(r2_hidden(esk2_3(X31,X32,X33),esk3_3(X31,X32,X33))|~r2_hidden(esk2_3(X31,X32,X33),X33)|X33=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31)))&(r1_xboole_0(X32,esk3_3(X31,X32,X33))|~r2_hidden(esk2_3(X31,X32,X33),X33)|X33=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))))&(r2_hidden(esk2_3(X31,X32,X33),X33)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X31)))|(~v3_pre_topc(X39,X31)|~r2_hidden(esk2_3(X31,X32,X33),X39)|~r1_xboole_0(X32,X39)))|X33=k2_pre_topc(X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).
% 0.20/0.45  fof(c_0_56, plain, ![X44, X45, X46, X47]:(((~v2_struct_0(X44)|~r2_hidden(X46,k2_pre_topc(X44,X45))|~m1_subset_1(X46,u1_struct_0(X44))|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44))&(~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X44)))|(~v3_pre_topc(X47,X44)|~r2_hidden(X46,X47)|~r1_xboole_0(X45,X47))|~r2_hidden(X46,k2_pre_topc(X44,X45))|~m1_subset_1(X46,u1_struct_0(X44))|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44)))&((m1_subset_1(esk4_3(X44,X45,X46),k1_zfmisc_1(u1_struct_0(X44)))|v2_struct_0(X44)|r2_hidden(X46,k2_pre_topc(X44,X45))|~m1_subset_1(X46,u1_struct_0(X44))|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44))&(((v3_pre_topc(esk4_3(X44,X45,X46),X44)|v2_struct_0(X44)|r2_hidden(X46,k2_pre_topc(X44,X45))|~m1_subset_1(X46,u1_struct_0(X44))|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44))&(r2_hidden(X46,esk4_3(X44,X45,X46))|v2_struct_0(X44)|r2_hidden(X46,k2_pre_topc(X44,X45))|~m1_subset_1(X46,u1_struct_0(X44))|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44)))&(r1_xboole_0(X45,esk4_3(X44,X45,X46))|v2_struct_0(X44)|r2_hidden(X46,k2_pre_topc(X44,X45))|~m1_subset_1(X46,u1_struct_0(X44))|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).
% 0.20/0.45  fof(c_0_57, plain, ![X28, X29, X30]:(~r2_hidden(X28,X29)|~m1_subset_1(X29,k1_zfmisc_1(X30))|m1_subset_1(X28,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.45  fof(c_0_58, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.45  fof(c_0_59, plain, ![X53, X54]:((~v4_pre_topc(X54,X53)|v3_pre_topc(k3_subset_1(u1_struct_0(X53),X54),X53)|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|~l1_pre_topc(X53))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X53),X54),X53)|v4_pre_topc(X54,X53)|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|~l1_pre_topc(X53))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.20/0.45  cnf(c_0_60, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.45  cnf(c_0_61, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_30]), c_0_38]), c_0_38])).
% 0.20/0.45  cnf(c_0_62, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.45  cnf(c_0_63, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.45  fof(c_0_64, plain, ![X52]:(~l1_pre_topc(X52)|k2_pre_topc(X52,k2_struct_0(X52))=k2_struct_0(X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).
% 0.20/0.45  cnf(c_0_65, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.45  cnf(c_0_66, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.45  cnf(c_0_67, plain, (r2_hidden(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k2_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.45  cnf(c_0_68, plain, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X4,X1)|~r2_hidden(X3,k2_pre_topc(X2,X4))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.45  cnf(c_0_69, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.45  cnf(c_0_70, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.45  cnf(c_0_71, plain, (v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.45  cnf(c_0_72, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_60, c_0_38])).
% 0.20/0.46  cnf(c_0_73, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_49]), c_0_62]), c_0_63])).
% 0.20/0.46  fof(c_0_74, plain, ![X42, X43]:((~v4_pre_topc(X43,X42)|k2_pre_topc(X42,X43)=X43|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|~l1_pre_topc(X42))&(~v2_pre_topc(X42)|k2_pre_topc(X42,X43)!=X43|v4_pre_topc(X43,X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|~l1_pre_topc(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.46  cnf(c_0_75, plain, (k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.46  cnf(c_0_76, negated_conjecture, (k2_struct_0(esk5_0)=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.46  cnf(c_0_77, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k2_pre_topc(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.46  cnf(c_0_78, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_67, c_0_42])).
% 0.20/0.46  cnf(c_0_79, plain, (r1_xboole_0(X1,esk3_3(X2,X1,X3))|X3=k2_pre_topc(X2,X1)|~r2_hidden(esk2_3(X2,X1,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.46  cnf(c_0_80, plain, (v3_pre_topc(esk3_3(X1,X2,X3),X1)|X3=k2_pre_topc(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.46  fof(c_0_81, plain, ![X49, X50]:((~v1_tops_1(X50,X49)|k2_pre_topc(X49,X50)=k2_struct_0(X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|~l1_pre_topc(X49))&(k2_pre_topc(X49,X50)!=k2_struct_0(X49)|v1_tops_1(X50,X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|~l1_pre_topc(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.20/0.46  cnf(c_0_82, plain, (~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X3,k2_pre_topc(X2,X4))|~r2_hidden(X3,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_xboole_0(X4,X1)), inference(csr,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.46  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  fof(c_0_84, plain, ![X23]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.46  cnf(c_0_85, plain, (r1_xboole_0(X1,X2)|k1_setfam_1(k2_tarski(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_70, c_0_30])).
% 0.20/0.46  cnf(c_0_86, plain, (v3_pre_topc(k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)),X1)|~v4_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_71, c_0_42])).
% 0.20/0.46  cnf(c_0_87, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_42]), c_0_63]), c_0_73])).
% 0.20/0.46  cnf(c_0_88, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.46  cnf(c_0_89, negated_conjecture, (k2_pre_topc(esk5_0,u1_struct_0(esk5_0))=u1_struct_0(esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_66]), c_0_76]), c_0_76])).
% 0.20/0.46  cnf(c_0_90, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  fof(c_0_91, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|(~r2_hidden(X22,X21)|r2_hidden(X22,X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.46  cnf(c_0_92, plain, (r2_hidden(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3))|X3=k2_pre_topc(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.46  cnf(c_0_93, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_42]), c_0_78])).
% 0.20/0.46  cnf(c_0_94, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|r1_xboole_0(X2,esk3_3(X1,X2,u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_42]), c_0_78])).
% 0.20/0.46  cnf(c_0_95, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|v3_pre_topc(esk3_3(X1,X2,u1_struct_0(X1)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_42]), c_0_78])).
% 0.20/0.46  cnf(c_0_96, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.46  cnf(c_0_97, negated_conjecture, (~v3_pre_topc(X1,esk5_0)|~r2_hidden(X2,k2_pre_topc(esk5_0,esk6_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_66])])).
% 0.20/0.46  cnf(c_0_98, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.46  cnf(c_0_99, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_85, c_0_49])).
% 0.20/0.46  cnf(c_0_100, plain, (v3_pre_topc(k1_xboole_0,X1)|~v4_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.46  cnf(c_0_101, negated_conjecture, (v4_pre_topc(u1_struct_0(esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_66]), c_0_42])])).
% 0.20/0.46  cnf(c_0_102, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.46  cnf(c_0_103, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),esk3_3(X1,X2,u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_42]), c_0_78])).
% 0.20/0.46  cnf(c_0_104, negated_conjecture, (v1_tops_1(esk6_0,esk5_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_pre_topc(X1,esk5_0)|~r1_xboole_0(esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  cnf(c_0_105, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|m1_subset_1(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_83]), c_0_66])])).
% 0.20/0.46  cnf(c_0_106, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|r1_xboole_0(esk6_0,esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_83]), c_0_66])])).
% 0.20/0.46  cnf(c_0_107, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|v3_pre_topc(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_83]), c_0_66])])).
% 0.20/0.46  cnf(c_0_108, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|~v1_tops_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_83]), c_0_76]), c_0_66])])).
% 0.20/0.46  cnf(c_0_109, negated_conjecture, (~v3_pre_topc(k1_xboole_0,esk5_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])])).
% 0.20/0.46  cnf(c_0_110, negated_conjecture, (v3_pre_topc(k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_66])])).
% 0.20/0.46  cnf(c_0_111, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_102, c_0_98])).
% 0.20/0.46  cnf(c_0_112, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.46  cnf(c_0_113, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|r2_hidden(esk2_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_83]), c_0_66])])).
% 0.20/0.46  cnf(c_0_114, negated_conjecture, (esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0))=k1_xboole_0|k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106]), c_0_107]), c_0_108])).
% 0.20/0.46  cnf(c_0_115, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110])]), c_0_111])).
% 0.20/0.46  cnf(c_0_116, negated_conjecture, (v1_tops_1(X1,esk5_0)|k2_pre_topc(esk5_0,X1)!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_76]), c_0_66])])).
% 0.20/0.46  cnf(c_0_117, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 0.20/0.46  fof(c_0_118, plain, ![X51]:(~v2_pre_topc(X51)|~l1_pre_topc(X51)|v3_pre_topc(k2_struct_0(X51),X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.20/0.46  cnf(c_0_119, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  cnf(c_0_120, negated_conjecture, (v1_tops_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_83])])).
% 0.20/0.46  cnf(c_0_121, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  cnf(c_0_122, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  cnf(c_0_123, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.46  cnf(c_0_124, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_98]), c_0_49]), c_0_62])).
% 0.20/0.46  cnf(c_0_125, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.20/0.46  cnf(c_0_126, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k2_pre_topc(X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X4,X1)|~r2_hidden(esk2_3(X1,X2,X3),X4)|~r1_xboole_0(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.46  cnf(c_0_127, negated_conjecture, (~v3_pre_topc(X1,esk5_0)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(esk6_0,X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_117]), c_0_102])).
% 0.20/0.46  cnf(c_0_128, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120])])).
% 0.20/0.46  cnf(c_0_129, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_120])])).
% 0.20/0.46  cnf(c_0_130, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_120])])).
% 0.20/0.46  cnf(c_0_131, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.46  cnf(c_0_132, plain, (v4_pre_topc(k1_xboole_0,X1)|~v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_98]), c_0_124])).
% 0.20/0.46  cnf(c_0_133, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_90]), c_0_76]), c_0_66])])).
% 0.20/0.46  cnf(c_0_134, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_98])).
% 0.20/0.46  cnf(c_0_135, plain, (X1=k2_pre_topc(X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|~v3_pre_topc(u1_struct_0(X2),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_xboole_0(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_42]), c_0_67])).
% 0.20/0.46  cnf(c_0_136, negated_conjecture, (~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_129]), c_0_130])])).
% 0.20/0.46  cnf(c_0_137, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_131, c_0_98])).
% 0.20/0.46  cnf(c_0_138, negated_conjecture, (v4_pre_topc(k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_66])])).
% 0.20/0.46  cnf(c_0_139, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_134])).
% 0.20/0.46  cnf(c_0_140, negated_conjecture, (esk7_0!=k1_xboole_0|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  cnf(c_0_141, negated_conjecture, (k2_pre_topc(esk5_0,X1)=esk7_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_128]), c_0_133]), c_0_66])]), c_0_136])).
% 0.20/0.46  cnf(c_0_142, negated_conjecture, (k2_pre_topc(esk5_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_66])])).
% 0.20/0.46  cnf(c_0_143, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_85, c_0_139])).
% 0.20/0.46  cnf(c_0_144, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_120])])).
% 0.20/0.46  cnf(c_0_145, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_98]), c_0_142]), c_0_143])]), c_0_144]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 146
% 0.20/0.46  # Proof object clause steps            : 97
% 0.20/0.46  # Proof object formula steps           : 49
% 0.20/0.46  # Proof object conjectures             : 38
% 0.20/0.46  # Proof object clause conjectures      : 35
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 39
% 0.20/0.46  # Proof object initial formulas used   : 24
% 0.20/0.46  # Proof object generating inferences   : 41
% 0.20/0.46  # Proof object simplifying inferences  : 87
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 24
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 51
% 0.20/0.46  # Removed in clause preprocessing      : 3
% 0.20/0.46  # Initial clauses in saturation        : 48
% 0.20/0.46  # Processed clauses                    : 381
% 0.20/0.46  # ...of these trivial                  : 2
% 0.20/0.46  # ...subsumed                          : 58
% 0.20/0.46  # ...remaining for further processing  : 321
% 0.20/0.46  # Other redundant clauses eliminated   : 6
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 8
% 0.20/0.46  # Backward-rewritten                   : 57
% 0.20/0.46  # Generated clauses                    : 513
% 0.20/0.46  # ...of the previous two non-trivial   : 491
% 0.20/0.46  # Contextual simplify-reflections      : 30
% 0.20/0.46  # Paramodulations                      : 507
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 6
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 204
% 0.20/0.46  #    Positive orientable unit clauses  : 38
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 3
% 0.20/0.46  #    Non-unit-clauses                  : 163
% 0.20/0.46  # Current number of unprocessed clauses: 188
% 0.20/0.46  # ...number of literals in the above   : 795
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 115
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 8965
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 3019
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 60
% 0.20/0.46  # Unit Clause-clause subsumption calls : 338
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 34
% 0.20/0.46  # BW rewrite match successes           : 8
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 18770
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.102 s
% 0.20/0.46  # System time              : 0.007 s
% 0.20/0.46  # Total time               : 0.109 s
% 0.20/0.46  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
