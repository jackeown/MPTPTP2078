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
% DateTime   : Thu Dec  3 11:11:54 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  128 (2570 expanded)
%              Number of clauses        :   83 (1095 expanded)
%              Number of leaves         :   22 ( 656 expanded)
%              Depth                    :   16
%              Number of atoms          :  467 (15318 expanded)
%              Number of equality atoms :   97 (2727 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   76 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_22,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X10] : k3_xboole_0(X10,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | k3_subset_1(X16,X17) = k4_xboole_0(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,negated_conjecture,(
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

fof(c_0_33,plain,(
    ! [X39] :
      ( ~ l1_struct_0(X39)
      | k2_struct_0(X39) = u1_struct_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_34,plain,(
    ! [X40] :
      ( ~ l1_pre_topc(X40)
      | l1_struct_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_35,plain,(
    ! [X18] : m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_36,plain,(
    ! [X15] : k2_subset_1(X15) = X15 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_37,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,X14) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_38,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_39,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_40,plain,(
    ! [X24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_26])).

fof(c_0_43,plain,(
    ! [X50] :
      ( ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | v3_pre_topc(k2_struct_0(X50),X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

fof(c_0_44,negated_conjecture,(
    ! [X56] :
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
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | X56 = k1_xboole_0
        | ~ v3_pre_topc(X56,esk5_0)
        | ~ r1_xboole_0(esk6_0,X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])])])).

cnf(c_0_45,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_47,plain,(
    ! [X30,X31,X32,X33,X34,X38] :
      ( ( ~ r2_hidden(X33,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ v3_pre_topc(X34,X30)
        | ~ r2_hidden(X33,X34)
        | ~ r1_xboole_0(X31,X34)
        | ~ r2_hidden(X33,u1_struct_0(X30))
        | X32 != k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk1_4(X30,X31,X32,X33),k1_zfmisc_1(u1_struct_0(X30)))
        | r2_hidden(X33,X32)
        | ~ r2_hidden(X33,u1_struct_0(X30))
        | X32 != k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( v3_pre_topc(esk1_4(X30,X31,X32,X33),X30)
        | r2_hidden(X33,X32)
        | ~ r2_hidden(X33,u1_struct_0(X30))
        | X32 != k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(X33,esk1_4(X30,X31,X32,X33))
        | r2_hidden(X33,X32)
        | ~ r2_hidden(X33,u1_struct_0(X30))
        | X32 != k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( r1_xboole_0(X31,esk1_4(X30,X31,X32,X33))
        | r2_hidden(X33,X32)
        | ~ r2_hidden(X33,u1_struct_0(X30))
        | X32 != k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(esk2_3(X30,X31,X32),u1_struct_0(X30))
        | X32 = k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk3_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r2_hidden(esk2_3(X30,X31,X32),X32)
        | X32 = k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( v3_pre_topc(esk3_3(X30,X31,X32),X30)
        | ~ r2_hidden(esk2_3(X30,X31,X32),X32)
        | X32 = k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(esk2_3(X30,X31,X32),esk3_3(X30,X31,X32))
        | ~ r2_hidden(esk2_3(X30,X31,X32),X32)
        | X32 = k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( r1_xboole_0(X31,esk3_3(X30,X31,X32))
        | ~ r2_hidden(esk2_3(X30,X31,X32),X32)
        | X32 = k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(esk2_3(X30,X31,X32),X32)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ v3_pre_topc(X38,X30)
        | ~ r2_hidden(esk2_3(X30,X31,X32),X38)
        | ~ r1_xboole_0(X31,X38)
        | X32 = k2_pre_topc(X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_50,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_53,plain,(
    ! [X51,X52] :
      ( ( ~ v4_pre_topc(X52,X51)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X51),X52),X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ l1_pre_topc(X51) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X51),X52),X51)
        | v4_pre_topc(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ l1_pre_topc(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_54,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_57,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_63,plain,(
    ! [X43,X44,X45,X46] :
      ( ( ~ v2_struct_0(X43)
        | ~ r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) )
      & ( ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ v3_pre_topc(X46,X43)
        | ~ r2_hidden(X45,X46)
        | ~ r1_xboole_0(X44,X46)
        | ~ r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) )
      & ( m1_subset_1(esk4_3(X43,X44,X45),k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) )
      & ( v3_pre_topc(esk4_3(X43,X44,X45),X43)
        | v2_struct_0(X43)
        | r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) )
      & ( r2_hidden(X45,esk4_3(X43,X44,X45))
        | v2_struct_0(X43)
        | r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) )
      & ( r1_xboole_0(X44,esk4_3(X43,X44,X45))
        | v2_struct_0(X43)
        | r2_hidden(X45,k2_pre_topc(X43,X44))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).

fof(c_0_64,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | m1_subset_1(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_30])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_26]),c_0_30]),c_0_30])).

fof(c_0_68,plain,(
    ! [X41,X42] :
      ( ( ~ v4_pre_topc(X42,X41)
        | k2_pre_topc(X41,X42) = X42
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) )
      & ( ~ v2_pre_topc(X41)
        | k2_pre_topc(X41,X42) != X42
        | v4_pre_topc(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_69,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_42]),c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(k2_struct_0(esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_72,negated_conjecture,
    ( k2_struct_0(esk5_0) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_73,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k2_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_74,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,esk3_3(X2,X1,X3))
    | X3 = k2_pre_topc(X2,X1)
    | ~ r2_hidden(esk2_3(X2,X1,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_76,plain,
    ( v3_pre_topc(esk3_3(X1,X2,X3),X1)
    | X3 = k2_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_77,plain,(
    ! [X48,X49] :
      ( ( ~ v1_tops_1(X49,X48)
        | k2_pre_topc(X48,X49) = k2_struct_0(X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ l1_pre_topc(X48) )
      & ( k2_pre_topc(X48,X49) != k2_struct_0(X48)
        | v1_tops_1(X49,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

cnf(c_0_78,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X4,X1)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_80,plain,
    ( r1_xboole_0(X1,X2)
    | k1_setfam_1(k2_tarski(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_65,c_0_26])).

cnf(c_0_81,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_82,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_83,plain,
    ( v4_pre_topc(k1_xboole_0,X1)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_55]),c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

fof(c_0_85,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ r2_hidden(X23,X22)
      | r2_hidden(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_86,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3))
    | X3 = k2_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_87,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | m1_subset_1(esk3_3(X1,X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_62]),c_0_74])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_89,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | r1_xboole_0(X2,esk3_3(X1,X2,u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_62]),c_0_74])).

cnf(c_0_90,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | v3_pre_topc(esk3_3(X1,X2,u1_struct_0(X1)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_62]),c_0_74])).

cnf(c_0_91,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_92,plain,
    ( ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X4))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_xboole_0(X4,X1) ),
    inference(csr,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_93,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_94,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_55])).

cnf(c_0_95,negated_conjecture,
    ( v4_pre_topc(k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_59])])).

cnf(c_0_96,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_97,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),esk3_3(X1,X2,u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_62]),c_0_74])).

cnf(c_0_98,negated_conjecture,
    ( v1_tops_1(esk6_0,esk5_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_99,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_59])])).

cnf(c_0_100,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | r1_xboole_0(esk6_0,esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_88]),c_0_59])])).

cnf(c_0_101,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | v3_pre_topc(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_88]),c_0_59])])).

cnf(c_0_102,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_88]),c_0_72]),c_0_59])])).

cnf(c_0_103,plain,
    ( ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,k2_pre_topc(X2,k1_xboole_0))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_55]),c_0_93])])).

cnf(c_0_104,negated_conjecture,
    ( k2_pre_topc(esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_59])])).

cnf(c_0_105,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_55])).

cnf(c_0_106,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_107,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | r2_hidden(esk2_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_88]),c_0_59])])).

cnf(c_0_108,negated_conjecture,
    ( esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)) = k1_xboole_0
    | k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),c_0_101]),c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_99]),c_0_59]),c_0_104])]),c_0_105]),c_0_101])).

cnf(c_0_110,negated_conjecture,
    ( v1_tops_1(X1,esk5_0)
    | k2_pre_topc(esk5_0,X1) != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_72]),c_0_59])])).

cnf(c_0_111,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,k2_pre_topc(esk5_0,esk6_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_88]),c_0_59])])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_114,negated_conjecture,
    ( v1_tops_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_88])])).

cnf(c_0_115,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0)
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_116,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0)
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_117,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X4)
    | ~ r1_xboole_0(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_118,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_111]),c_0_96])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114])])).

cnf(c_0_120,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_114])])).

cnf(c_0_121,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_114])])).

cnf(c_0_122,plain,
    ( X1 = k2_pre_topc(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_xboole_0(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_62]),c_0_61])).

cnf(c_0_123,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120]),c_0_121])])).

cnf(c_0_124,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_125,negated_conjecture,
    ( k2_pre_topc(esk5_0,X1) = esk7_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_119]),c_0_84]),c_0_59])]),c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_114])])).

cnf(c_0_127,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_55]),c_0_104]),c_0_93])]),c_0_126]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.30  % Computer   : n009.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 16:00:41 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  # Version: 2.5pre002
% 0.10/0.30  # No SInE strategy applied
% 0.10/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.15/0.39  # and selection function SelectCQArNTNpEqFirst.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.030 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.15/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.15/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.15/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.15/0.39  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.15/0.39  fof(t80_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X3!=k1_xboole_0&v3_pre_topc(X3,X1))&r1_xboole_0(X2,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tops_1)).
% 0.15/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.15/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.15/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.15/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.15/0.39  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.15/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.15/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.15/0.39  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.15/0.39  fof(d13_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k2_pre_topc(X1,X2)<=>![X4]:(r2_hidden(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X5,X1)&r2_hidden(X4,X5))&r1_xboole_0(X2,X5)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_pre_topc)).
% 0.15/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.15/0.39  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 0.15/0.39  fof(t54_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>(~(v2_struct_0(X1))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_pre_topc)).
% 0.15/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.15/0.39  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.15/0.39  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 0.15/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.15/0.39  fof(c_0_22, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.15/0.39  fof(c_0_23, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.15/0.39  fof(c_0_24, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.15/0.39  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.39  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.39  fof(c_0_27, plain, ![X10]:k3_xboole_0(X10,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.15/0.39  fof(c_0_28, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|k3_subset_1(X16,X17)=k4_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.15/0.39  cnf(c_0_29, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.15/0.39  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.39  cnf(c_0_31, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.39  fof(c_0_32, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X3!=k1_xboole_0&v3_pre_topc(X3,X1))&r1_xboole_0(X2,X3)))))))), inference(assume_negation,[status(cth)],[t80_tops_1])).
% 0.15/0.39  fof(c_0_33, plain, ![X39]:(~l1_struct_0(X39)|k2_struct_0(X39)=u1_struct_0(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.15/0.39  fof(c_0_34, plain, ![X40]:(~l1_pre_topc(X40)|l1_struct_0(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.15/0.39  fof(c_0_35, plain, ![X18]:m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.15/0.39  fof(c_0_36, plain, ![X15]:k2_subset_1(X15)=X15, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.15/0.39  fof(c_0_37, plain, ![X14]:k4_xboole_0(k1_xboole_0,X14)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.15/0.39  fof(c_0_38, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.15/0.39  cnf(c_0_39, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.15/0.39  fof(c_0_40, plain, ![X24]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.15/0.39  cnf(c_0_41, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.15/0.39  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_26])).
% 0.15/0.39  fof(c_0_43, plain, ![X50]:(~v2_pre_topc(X50)|~l1_pre_topc(X50)|v3_pre_topc(k2_struct_0(X50),X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.15/0.39  fof(c_0_44, negated_conjecture, ![X56]:((v2_pre_topc(esk5_0)&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(((m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_tops_1(esk6_0,esk5_0))&(((esk7_0!=k1_xboole_0|~v1_tops_1(esk6_0,esk5_0))&(v3_pre_topc(esk7_0,esk5_0)|~v1_tops_1(esk6_0,esk5_0)))&(r1_xboole_0(esk6_0,esk7_0)|~v1_tops_1(esk6_0,esk5_0))))&(v1_tops_1(esk6_0,esk5_0)|(~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(esk5_0)))|(X56=k1_xboole_0|~v3_pre_topc(X56,esk5_0)|~r1_xboole_0(esk6_0,X56))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])])])).
% 0.15/0.39  cnf(c_0_45, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.15/0.39  cnf(c_0_46, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.15/0.39  fof(c_0_47, plain, ![X30, X31, X32, X33, X34, X38]:(((~r2_hidden(X33,X32)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X30)))|(~v3_pre_topc(X34,X30)|~r2_hidden(X33,X34)|~r1_xboole_0(X31,X34)))|~r2_hidden(X33,u1_struct_0(X30))|X32!=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&((m1_subset_1(esk1_4(X30,X31,X32,X33),k1_zfmisc_1(u1_struct_0(X30)))|r2_hidden(X33,X32)|~r2_hidden(X33,u1_struct_0(X30))|X32!=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(((v3_pre_topc(esk1_4(X30,X31,X32,X33),X30)|r2_hidden(X33,X32)|~r2_hidden(X33,u1_struct_0(X30))|X32!=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(r2_hidden(X33,esk1_4(X30,X31,X32,X33))|r2_hidden(X33,X32)|~r2_hidden(X33,u1_struct_0(X30))|X32!=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30)))&(r1_xboole_0(X31,esk1_4(X30,X31,X32,X33))|r2_hidden(X33,X32)|~r2_hidden(X33,u1_struct_0(X30))|X32!=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30)))))&((r2_hidden(esk2_3(X30,X31,X32),u1_struct_0(X30))|X32=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(((m1_subset_1(esk3_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))|~r2_hidden(esk2_3(X30,X31,X32),X32)|X32=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(((v3_pre_topc(esk3_3(X30,X31,X32),X30)|~r2_hidden(esk2_3(X30,X31,X32),X32)|X32=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(r2_hidden(esk2_3(X30,X31,X32),esk3_3(X30,X31,X32))|~r2_hidden(esk2_3(X30,X31,X32),X32)|X32=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30)))&(r1_xboole_0(X31,esk3_3(X30,X31,X32))|~r2_hidden(esk2_3(X30,X31,X32),X32)|X32=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))))&(r2_hidden(esk2_3(X30,X31,X32),X32)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X30)))|(~v3_pre_topc(X38,X30)|~r2_hidden(esk2_3(X30,X31,X32),X38)|~r1_xboole_0(X31,X38)))|X32=k2_pre_topc(X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).
% 0.15/0.39  cnf(c_0_48, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.15/0.39  cnf(c_0_49, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.15/0.39  fof(c_0_50, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.15/0.39  cnf(c_0_51, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.15/0.39  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.15/0.39  fof(c_0_53, plain, ![X51, X52]:((~v4_pre_topc(X52,X51)|v3_pre_topc(k3_subset_1(u1_struct_0(X51),X52),X51)|~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))|~l1_pre_topc(X51))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X51),X52),X51)|v4_pre_topc(X52,X51)|~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))|~l1_pre_topc(X51))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.15/0.39  cnf(c_0_54, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_39, c_0_30])).
% 0.15/0.39  cnf(c_0_55, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.39  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.15/0.39  cnf(c_0_57, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.15/0.39  cnf(c_0_58, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.15/0.39  cnf(c_0_59, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.15/0.39  cnf(c_0_60, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.15/0.39  cnf(c_0_61, plain, (r2_hidden(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k2_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.15/0.39  cnf(c_0_62, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.15/0.39  fof(c_0_63, plain, ![X43, X44, X45, X46]:(((~v2_struct_0(X43)|~r2_hidden(X45,k2_pre_topc(X43,X44))|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))&(~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X43)))|(~v3_pre_topc(X46,X43)|~r2_hidden(X45,X46)|~r1_xboole_0(X44,X46))|~r2_hidden(X45,k2_pre_topc(X43,X44))|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43)))&((m1_subset_1(esk4_3(X43,X44,X45),k1_zfmisc_1(u1_struct_0(X43)))|v2_struct_0(X43)|r2_hidden(X45,k2_pre_topc(X43,X44))|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))&(((v3_pre_topc(esk4_3(X43,X44,X45),X43)|v2_struct_0(X43)|r2_hidden(X45,k2_pre_topc(X43,X44))|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))&(r2_hidden(X45,esk4_3(X43,X44,X45))|v2_struct_0(X43)|r2_hidden(X45,k2_pre_topc(X43,X44))|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43)))&(r1_xboole_0(X44,esk4_3(X43,X44,X45))|v2_struct_0(X43)|r2_hidden(X45,k2_pre_topc(X43,X44))|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|~l1_pre_topc(X43))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).
% 0.15/0.39  fof(c_0_64, plain, ![X27, X28, X29]:(~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X29))|m1_subset_1(X27,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.15/0.39  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.15/0.39  cnf(c_0_66, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_51, c_0_30])).
% 0.15/0.39  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_26]), c_0_30]), c_0_30])).
% 0.15/0.39  fof(c_0_68, plain, ![X41, X42]:((~v4_pre_topc(X42,X41)|k2_pre_topc(X41,X42)=X42|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X41))&(~v2_pre_topc(X41)|k2_pre_topc(X41,X42)!=X42|v4_pre_topc(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.15/0.39  cnf(c_0_69, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.15/0.39  cnf(c_0_70, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_42]), c_0_56])).
% 0.15/0.39  cnf(c_0_71, negated_conjecture, (v3_pre_topc(k2_struct_0(esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.15/0.39  cnf(c_0_72, negated_conjecture, (k2_struct_0(esk5_0)=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_59])).
% 0.15/0.39  cnf(c_0_73, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k2_pre_topc(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.15/0.39  cnf(c_0_74, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.15/0.39  cnf(c_0_75, plain, (r1_xboole_0(X1,esk3_3(X2,X1,X3))|X3=k2_pre_topc(X2,X1)|~r2_hidden(esk2_3(X2,X1,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.15/0.39  cnf(c_0_76, plain, (v3_pre_topc(esk3_3(X1,X2,X3),X1)|X3=k2_pre_topc(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.15/0.39  fof(c_0_77, plain, ![X48, X49]:((~v1_tops_1(X49,X48)|k2_pre_topc(X48,X49)=k2_struct_0(X48)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|~l1_pre_topc(X48))&(k2_pre_topc(X48,X49)!=k2_struct_0(X48)|v1_tops_1(X49,X48)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|~l1_pre_topc(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.15/0.39  cnf(c_0_78, plain, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X4,X1)|~r2_hidden(X3,k2_pre_topc(X2,X4))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.15/0.39  cnf(c_0_79, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.15/0.39  cnf(c_0_80, plain, (r1_xboole_0(X1,X2)|k1_setfam_1(k2_tarski(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_65, c_0_26])).
% 0.15/0.39  cnf(c_0_81, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.15/0.39  cnf(c_0_82, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.15/0.39  cnf(c_0_83, plain, (v4_pre_topc(k1_xboole_0,X1)|~v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_55]), c_0_70])).
% 0.15/0.39  cnf(c_0_84, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk5_0)), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.15/0.39  fof(c_0_85, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~r2_hidden(X23,X22)|r2_hidden(X23,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.15/0.39  cnf(c_0_86, plain, (r2_hidden(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3))|X3=k2_pre_topc(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.15/0.39  cnf(c_0_87, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_62]), c_0_74])).
% 0.15/0.39  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.15/0.39  cnf(c_0_89, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|r1_xboole_0(X2,esk3_3(X1,X2,u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_62]), c_0_74])).
% 0.15/0.39  cnf(c_0_90, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|v3_pre_topc(esk3_3(X1,X2,u1_struct_0(X1)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_62]), c_0_74])).
% 0.15/0.39  cnf(c_0_91, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.15/0.39  cnf(c_0_92, plain, (~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X3,k2_pre_topc(X2,X4))|~r2_hidden(X3,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_xboole_0(X4,X1)), inference(csr,[status(thm)],[c_0_78, c_0_79])).
% 0.15/0.39  cnf(c_0_93, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.15/0.39  cnf(c_0_94, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_82, c_0_55])).
% 0.15/0.39  cnf(c_0_95, negated_conjecture, (v4_pre_topc(k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_59])])).
% 0.15/0.39  cnf(c_0_96, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.15/0.39  cnf(c_0_97, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),esk3_3(X1,X2,u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_62]), c_0_74])).
% 0.15/0.39  cnf(c_0_98, negated_conjecture, (v1_tops_1(esk6_0,esk5_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_pre_topc(X1,esk5_0)|~r1_xboole_0(esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.15/0.39  cnf(c_0_99, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|m1_subset_1(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_59])])).
% 0.15/0.39  cnf(c_0_100, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|r1_xboole_0(esk6_0,esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_88]), c_0_59])])).
% 0.15/0.39  cnf(c_0_101, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|v3_pre_topc(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_88]), c_0_59])])).
% 0.15/0.39  cnf(c_0_102, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|~v1_tops_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_88]), c_0_72]), c_0_59])])).
% 0.15/0.39  cnf(c_0_103, plain, (~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X3,k2_pre_topc(X2,k1_xboole_0))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_55]), c_0_93])])).
% 0.15/0.39  cnf(c_0_104, negated_conjecture, (k2_pre_topc(esk5_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_59])])).
% 0.15/0.39  cnf(c_0_105, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_96, c_0_55])).
% 0.15/0.39  cnf(c_0_106, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.15/0.39  cnf(c_0_107, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|r2_hidden(esk2_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_88]), c_0_59])])).
% 0.15/0.39  cnf(c_0_108, negated_conjecture, (esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0))=k1_xboole_0|k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), c_0_101]), c_0_102])).
% 0.15/0.39  cnf(c_0_109, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_99]), c_0_59]), c_0_104])]), c_0_105]), c_0_101])).
% 0.15/0.39  cnf(c_0_110, negated_conjecture, (v1_tops_1(X1,esk5_0)|k2_pre_topc(esk5_0,X1)!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_72]), c_0_59])])).
% 0.15/0.39  cnf(c_0_111, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])).
% 0.15/0.39  cnf(c_0_112, negated_conjecture, (~v3_pre_topc(X1,esk5_0)|~r2_hidden(X2,k2_pre_topc(esk5_0,esk6_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_88]), c_0_59])])).
% 0.15/0.39  cnf(c_0_113, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.15/0.39  cnf(c_0_114, negated_conjecture, (v1_tops_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_88])])).
% 0.15/0.39  cnf(c_0_115, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.15/0.39  cnf(c_0_116, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.15/0.39  cnf(c_0_117, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k2_pre_topc(X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X4,X1)|~r2_hidden(esk2_3(X1,X2,X3),X4)|~r1_xboole_0(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.15/0.39  cnf(c_0_118, negated_conjecture, (~v3_pre_topc(X1,esk5_0)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(esk6_0,X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_111]), c_0_96])).
% 0.15/0.39  cnf(c_0_119, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114])])).
% 0.15/0.39  cnf(c_0_120, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_114])])).
% 0.15/0.39  cnf(c_0_121, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_114])])).
% 0.15/0.39  cnf(c_0_122, plain, (X1=k2_pre_topc(X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|~v3_pre_topc(u1_struct_0(X2),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_xboole_0(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_62]), c_0_61])).
% 0.15/0.39  cnf(c_0_123, negated_conjecture, (~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120]), c_0_121])])).
% 0.15/0.39  cnf(c_0_124, negated_conjecture, (esk7_0!=k1_xboole_0|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.15/0.39  cnf(c_0_125, negated_conjecture, (k2_pre_topc(esk5_0,X1)=esk7_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_119]), c_0_84]), c_0_59])]), c_0_123])).
% 0.15/0.39  cnf(c_0_126, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_114])])).
% 0.15/0.39  cnf(c_0_127, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_55]), c_0_104]), c_0_93])]), c_0_126]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 128
% 0.15/0.39  # Proof object clause steps            : 83
% 0.15/0.39  # Proof object formula steps           : 45
% 0.15/0.39  # Proof object conjectures             : 35
% 0.15/0.39  # Proof object clause conjectures      : 32
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 35
% 0.15/0.39  # Proof object initial formulas used   : 22
% 0.15/0.39  # Proof object generating inferences   : 32
% 0.15/0.39  # Proof object simplifying inferences  : 76
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 23
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 49
% 0.15/0.39  # Removed in clause preprocessing      : 3
% 0.15/0.39  # Initial clauses in saturation        : 46
% 0.15/0.39  # Processed clauses                    : 513
% 0.15/0.39  # ...of these trivial                  : 4
% 0.15/0.39  # ...subsumed                          : 93
% 0.15/0.39  # ...remaining for further processing  : 416
% 0.15/0.39  # Other redundant clauses eliminated   : 6
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 26
% 0.15/0.39  # Backward-rewritten                   : 63
% 0.15/0.39  # Generated clauses                    : 1531
% 0.15/0.39  # ...of the previous two non-trivial   : 1524
% 0.15/0.39  # Contextual simplify-reflections      : 30
% 0.15/0.39  # Paramodulations                      : 1525
% 0.15/0.39  # Factorizations                       : 0
% 0.15/0.39  # Equation resolutions                 : 6
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 277
% 0.15/0.39  #    Positive orientable unit clauses  : 36
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 4
% 0.15/0.39  #    Non-unit-clauses                  : 237
% 0.15/0.39  # Current number of unprocessed clauses: 1065
% 0.15/0.39  # ...number of literals in the above   : 4336
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 137
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 11296
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 4733
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 113
% 0.15/0.39  # Unit Clause-clause subsumption calls : 436
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 43
% 0.15/0.39  # BW rewrite match successes           : 6
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 59416
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.086 s
% 0.15/0.39  # System time              : 0.006 s
% 0.15/0.39  # Total time               : 0.092 s
% 0.15/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
