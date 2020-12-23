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
% DateTime   : Thu Dec  3 11:11:53 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 (2471 expanded)
%              Number of clauses        :   82 (1052 expanded)
%              Number of leaves         :   21 ( 628 expanded)
%              Depth                    :   16
%              Number of atoms          :  469 (15249 expanded)
%              Number of equality atoms :   93 (2622 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   76 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

fof(c_0_21,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_23,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X12] : k3_xboole_0(X12,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_27,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k3_subset_1(X15,X16) = k4_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,negated_conjecture,(
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

fof(c_0_32,plain,(
    ! [X36] :
      ( ~ l1_struct_0(X36)
      | k2_struct_0(X36) = u1_struct_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_33,plain,(
    ! [X37] :
      ( ~ l1_pre_topc(X37)
      | l1_struct_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_34,plain,(
    ! [X17] : m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_35,plain,(
    ! [X14] : k2_subset_1(X14) = X14 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_36,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_37,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_25])).

fof(c_0_41,plain,(
    ! [X47] :
      ( ~ v2_pre_topc(X47)
      | ~ l1_pre_topc(X47)
      | v3_pre_topc(k2_struct_0(X47),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

fof(c_0_42,negated_conjecture,(
    ! [X53] :
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
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | X53 = k1_xboole_0
        | ~ v3_pre_topc(X53,esk5_0)
        | ~ r1_xboole_0(esk6_0,X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])])])).

cnf(c_0_43,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X27,X28,X29,X30,X31,X35] :
      ( ( ~ r2_hidden(X30,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ v3_pre_topc(X31,X27)
        | ~ r2_hidden(X30,X31)
        | ~ r1_xboole_0(X28,X31)
        | ~ r2_hidden(X30,u1_struct_0(X27))
        | X29 != k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk1_4(X27,X28,X29,X30),k1_zfmisc_1(u1_struct_0(X27)))
        | r2_hidden(X30,X29)
        | ~ r2_hidden(X30,u1_struct_0(X27))
        | X29 != k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( v3_pre_topc(esk1_4(X27,X28,X29,X30),X27)
        | r2_hidden(X30,X29)
        | ~ r2_hidden(X30,u1_struct_0(X27))
        | X29 != k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( r2_hidden(X30,esk1_4(X27,X28,X29,X30))
        | r2_hidden(X30,X29)
        | ~ r2_hidden(X30,u1_struct_0(X27))
        | X29 != k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( r1_xboole_0(X28,esk1_4(X27,X28,X29,X30))
        | r2_hidden(X30,X29)
        | ~ r2_hidden(X30,u1_struct_0(X27))
        | X29 != k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( r2_hidden(esk2_3(X27,X28,X29),u1_struct_0(X27))
        | X29 = k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk3_3(X27,X28,X29),k1_zfmisc_1(u1_struct_0(X27)))
        | ~ r2_hidden(esk2_3(X27,X28,X29),X29)
        | X29 = k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( v3_pre_topc(esk3_3(X27,X28,X29),X27)
        | ~ r2_hidden(esk2_3(X27,X28,X29),X29)
        | X29 = k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( r2_hidden(esk2_3(X27,X28,X29),esk3_3(X27,X28,X29))
        | ~ r2_hidden(esk2_3(X27,X28,X29),X29)
        | X29 = k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( r1_xboole_0(X28,esk3_3(X27,X28,X29))
        | ~ r2_hidden(esk2_3(X27,X28,X29),X29)
        | X29 = k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( r2_hidden(esk2_3(X27,X28,X29),X29)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ v3_pre_topc(X35,X27)
        | ~ r2_hidden(esk2_3(X27,X28,X29),X35)
        | ~ r1_xboole_0(X28,X35)
        | X29 = k2_pre_topc(X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).

cnf(c_0_46,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_48,plain,(
    ! [X40,X41,X42,X43] :
      ( ( ~ v2_struct_0(X40)
        | ~ r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) )
      & ( ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ v3_pre_topc(X43,X40)
        | ~ r2_hidden(X42,X43)
        | ~ r1_xboole_0(X41,X43)
        | ~ r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(esk4_3(X40,X41,X42),k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) )
      & ( v3_pre_topc(esk4_3(X40,X41,X42),X40)
        | v2_struct_0(X40)
        | r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) )
      & ( r2_hidden(X42,esk4_3(X40,X41,X42))
        | v2_struct_0(X40)
        | r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) )
      & ( r1_xboole_0(X41,esk4_3(X40,X41,X42))
        | v2_struct_0(X40)
        | r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).

fof(c_0_49,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | m1_subset_1(X24,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_50,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_52,plain,(
    ! [X48,X49] :
      ( ( ~ v4_pre_topc(X49,X48)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X48),X49),X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ l1_pre_topc(X48) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X48),X49),X48)
        | v4_pre_topc(X49,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_53,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_29])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_56,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_59,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_60,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_62,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X4,X1)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_25]),c_0_25])).

fof(c_0_66,plain,(
    ! [X38,X39] :
      ( ( ~ v4_pre_topc(X39,X38)
        | k2_pre_topc(X38,X39) = X39
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( ~ v2_pre_topc(X38)
        | k2_pre_topc(X38,X39) != X39
        | v4_pre_topc(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_67,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_40]),c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( v3_pre_topc(k2_struct_0(esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_70,negated_conjecture,
    ( k2_struct_0(esk5_0) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_58])).

cnf(c_0_71,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k2_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_72,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,esk3_3(X2,X1,X3))
    | X3 = k2_pre_topc(X2,X1)
    | ~ r2_hidden(esk2_3(X2,X1,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_74,plain,
    ( v3_pre_topc(esk3_3(X1,X2,X3),X1)
    | X3 = k2_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_75,plain,(
    ! [X45,X46] :
      ( ( ~ v1_tops_1(X46,X45)
        | k2_pre_topc(X45,X46) = k2_struct_0(X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) )
      & ( k2_pre_topc(X45,X46) != k2_struct_0(X45)
        | v1_tops_1(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

cnf(c_0_76,plain,
    ( ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X4))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_xboole_0(X4,X1) ),
    inference(csr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,X2)
    | k1_setfam_1(k2_tarski(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_25])).

cnf(c_0_78,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_65])).

cnf(c_0_79,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_80,plain,
    ( v4_pre_topc(k1_xboole_0,X1)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_54]),c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_82,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ r2_hidden(X20,X19)
      | r2_hidden(X20,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_83,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3))
    | X3 = k2_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_84,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | m1_subset_1(esk3_3(X1,X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_61]),c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_86,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | r1_xboole_0(X2,esk3_3(X1,X2,u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_61]),c_0_72])).

cnf(c_0_87,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | v3_pre_topc(esk3_3(X1,X2,u1_struct_0(X1)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_61]),c_0_72])).

cnf(c_0_88,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_89,plain,
    ( ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,k2_pre_topc(X2,k1_xboole_0))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_54])).

cnf(c_0_90,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_91,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_54])).

cnf(c_0_92,negated_conjecture,
    ( v4_pre_topc(k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_58])])).

cnf(c_0_93,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_94,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),esk3_3(X1,X2,u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_61]),c_0_72])).

cnf(c_0_95,negated_conjecture,
    ( v1_tops_1(esk6_0,esk5_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_96,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_58])])).

cnf(c_0_97,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | r1_xboole_0(esk6_0,esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_85]),c_0_58])])).

cnf(c_0_98,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | v3_pre_topc(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_85]),c_0_58])])).

cnf(c_0_99,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_85]),c_0_70]),c_0_58])])).

cnf(c_0_100,plain,
    ( ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,k2_pre_topc(X2,k1_xboole_0))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_101,negated_conjecture,
    ( k2_pre_topc(esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_58])])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_54])).

cnf(c_0_103,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_104,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | r2_hidden(esk2_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_85]),c_0_58])])).

cnf(c_0_105,negated_conjecture,
    ( esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)) = k1_xboole_0
    | k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),c_0_98]),c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_96]),c_0_58]),c_0_101])]),c_0_102]),c_0_98])).

cnf(c_0_107,negated_conjecture,
    ( v1_tops_1(X1,esk5_0)
    | k2_pre_topc(esk5_0,X1) != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_70]),c_0_58])])).

cnf(c_0_108,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = u1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,k2_pre_topc(esk5_0,esk6_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_85]),c_0_58])])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_111,negated_conjecture,
    ( v1_tops_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_85])])).

cnf(c_0_112,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0)
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_113,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0)
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_114,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X4)
    | ~ r1_xboole_0(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_115,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_108]),c_0_93])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111])])).

cnf(c_0_117,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_111])])).

cnf(c_0_118,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_111])])).

cnf(c_0_119,plain,
    ( X1 = k2_pre_topc(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_xboole_0(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_61]),c_0_60])).

cnf(c_0_120,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_118])])).

cnf(c_0_121,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ v1_tops_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_122,negated_conjecture,
    ( k2_pre_topc(esk5_0,X1) = esk7_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_xboole_0(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_116]),c_0_81]),c_0_58])]),c_0_120])).

cnf(c_0_123,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_111])])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_54]),c_0_101]),c_0_90])]),c_0_123]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.42  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.029 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.42  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.42  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.42  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.42  fof(t80_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X3!=k1_xboole_0&v3_pre_topc(X3,X1))&r1_xboole_0(X2,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tops_1)).
% 0.20/0.42  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.42  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.42  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.42  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.42  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.42  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.20/0.42  fof(d13_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k2_pre_topc(X1,X2)<=>![X4]:(r2_hidden(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X5,X1)&r2_hidden(X4,X5))&r1_xboole_0(X2,X5)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_pre_topc)).
% 0.20/0.42  fof(t54_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>(~(v2_struct_0(X1))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_pre_topc)).
% 0.20/0.42  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.42  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.42  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 0.20/0.42  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.42  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 0.20/0.42  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.42  fof(c_0_21, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.42  fof(c_0_22, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.42  fof(c_0_23, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.42  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_25, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  fof(c_0_26, plain, ![X12]:k3_xboole_0(X12,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.42  fof(c_0_27, plain, ![X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|k3_subset_1(X15,X16)=k4_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.42  cnf(c_0_28, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.42  cnf(c_0_30, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  fof(c_0_31, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X3!=k1_xboole_0&v3_pre_topc(X3,X1))&r1_xboole_0(X2,X3)))))))), inference(assume_negation,[status(cth)],[t80_tops_1])).
% 0.20/0.42  fof(c_0_32, plain, ![X36]:(~l1_struct_0(X36)|k2_struct_0(X36)=u1_struct_0(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.42  fof(c_0_33, plain, ![X37]:(~l1_pre_topc(X37)|l1_struct_0(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.42  fof(c_0_34, plain, ![X17]:m1_subset_1(k2_subset_1(X17),k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.42  fof(c_0_35, plain, ![X14]:k2_subset_1(X14)=X14, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.42  fof(c_0_36, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.42  cnf(c_0_37, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  fof(c_0_38, plain, ![X21]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.42  cnf(c_0_39, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.42  cnf(c_0_40, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_25])).
% 0.20/0.42  fof(c_0_41, plain, ![X47]:(~v2_pre_topc(X47)|~l1_pre_topc(X47)|v3_pre_topc(k2_struct_0(X47),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.20/0.42  fof(c_0_42, negated_conjecture, ![X53]:((v2_pre_topc(esk5_0)&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(((m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_tops_1(esk6_0,esk5_0))&(((esk7_0!=k1_xboole_0|~v1_tops_1(esk6_0,esk5_0))&(v3_pre_topc(esk7_0,esk5_0)|~v1_tops_1(esk6_0,esk5_0)))&(r1_xboole_0(esk6_0,esk7_0)|~v1_tops_1(esk6_0,esk5_0))))&(v1_tops_1(esk6_0,esk5_0)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(esk5_0)))|(X53=k1_xboole_0|~v3_pre_topc(X53,esk5_0)|~r1_xboole_0(esk6_0,X53))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])])])).
% 0.20/0.42  cnf(c_0_43, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_44, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  fof(c_0_45, plain, ![X27, X28, X29, X30, X31, X35]:(((~r2_hidden(X30,X29)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X27)))|(~v3_pre_topc(X31,X27)|~r2_hidden(X30,X31)|~r1_xboole_0(X28,X31)))|~r2_hidden(X30,u1_struct_0(X27))|X29!=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&((m1_subset_1(esk1_4(X27,X28,X29,X30),k1_zfmisc_1(u1_struct_0(X27)))|r2_hidden(X30,X29)|~r2_hidden(X30,u1_struct_0(X27))|X29!=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(((v3_pre_topc(esk1_4(X27,X28,X29,X30),X27)|r2_hidden(X30,X29)|~r2_hidden(X30,u1_struct_0(X27))|X29!=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(r2_hidden(X30,esk1_4(X27,X28,X29,X30))|r2_hidden(X30,X29)|~r2_hidden(X30,u1_struct_0(X27))|X29!=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27)))&(r1_xboole_0(X28,esk1_4(X27,X28,X29,X30))|r2_hidden(X30,X29)|~r2_hidden(X30,u1_struct_0(X27))|X29!=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27)))))&((r2_hidden(esk2_3(X27,X28,X29),u1_struct_0(X27))|X29=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(((m1_subset_1(esk3_3(X27,X28,X29),k1_zfmisc_1(u1_struct_0(X27)))|~r2_hidden(esk2_3(X27,X28,X29),X29)|X29=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(((v3_pre_topc(esk3_3(X27,X28,X29),X27)|~r2_hidden(esk2_3(X27,X28,X29),X29)|X29=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(r2_hidden(esk2_3(X27,X28,X29),esk3_3(X27,X28,X29))|~r2_hidden(esk2_3(X27,X28,X29),X29)|X29=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27)))&(r1_xboole_0(X28,esk3_3(X27,X28,X29))|~r2_hidden(esk2_3(X27,X28,X29),X29)|X29=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))))&(r2_hidden(esk2_3(X27,X28,X29),X29)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X27)))|(~v3_pre_topc(X35,X27)|~r2_hidden(esk2_3(X27,X28,X29),X35)|~r1_xboole_0(X28,X35)))|X29=k2_pre_topc(X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).
% 0.20/0.42  cnf(c_0_46, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.42  cnf(c_0_47, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.42  fof(c_0_48, plain, ![X40, X41, X42, X43]:(((~v2_struct_0(X40)|~r2_hidden(X42,k2_pre_topc(X40,X41))|~m1_subset_1(X42,u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))&(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X40)))|(~v3_pre_topc(X43,X40)|~r2_hidden(X42,X43)|~r1_xboole_0(X41,X43))|~r2_hidden(X42,k2_pre_topc(X40,X41))|~m1_subset_1(X42,u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40)))&((m1_subset_1(esk4_3(X40,X41,X42),k1_zfmisc_1(u1_struct_0(X40)))|v2_struct_0(X40)|r2_hidden(X42,k2_pre_topc(X40,X41))|~m1_subset_1(X42,u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))&(((v3_pre_topc(esk4_3(X40,X41,X42),X40)|v2_struct_0(X40)|r2_hidden(X42,k2_pre_topc(X40,X41))|~m1_subset_1(X42,u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))&(r2_hidden(X42,esk4_3(X40,X41,X42))|v2_struct_0(X40)|r2_hidden(X42,k2_pre_topc(X40,X41))|~m1_subset_1(X42,u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40)))&(r1_xboole_0(X41,esk4_3(X40,X41,X42))|v2_struct_0(X40)|r2_hidden(X42,k2_pre_topc(X40,X41))|~m1_subset_1(X42,u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).
% 0.20/0.42  fof(c_0_49, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|m1_subset_1(X24,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.42  fof(c_0_50, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.42  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.42  fof(c_0_52, plain, ![X48, X49]:((~v4_pre_topc(X49,X48)|v3_pre_topc(k3_subset_1(u1_struct_0(X48),X49),X48)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|~l1_pre_topc(X48))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X48),X49),X48)|v4_pre_topc(X49,X48)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|~l1_pre_topc(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.20/0.42  cnf(c_0_53, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_37, c_0_29])).
% 0.20/0.42  cnf(c_0_54, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.42  cnf(c_0_55, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.42  cnf(c_0_56, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_59, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.42  cnf(c_0_60, plain, (r2_hidden(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k2_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.42  cnf(c_0_62, plain, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X4,X1)|~r2_hidden(X3,k2_pre_topc(X2,X4))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.42  cnf(c_0_63, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  cnf(c_0_64, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.42  cnf(c_0_65, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_25]), c_0_25])).
% 0.20/0.42  fof(c_0_66, plain, ![X38, X39]:((~v4_pre_topc(X39,X38)|k2_pre_topc(X38,X39)=X39|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))&(~v2_pre_topc(X38)|k2_pre_topc(X38,X39)!=X39|v4_pre_topc(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.42  cnf(c_0_67, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.42  cnf(c_0_68, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_40]), c_0_55])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (v3_pre_topc(k2_struct_0(esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (k2_struct_0(esk5_0)=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_58])).
% 0.20/0.42  cnf(c_0_71, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k2_pre_topc(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_72, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.42  cnf(c_0_73, plain, (r1_xboole_0(X1,esk3_3(X2,X1,X3))|X3=k2_pre_topc(X2,X1)|~r2_hidden(esk2_3(X2,X1,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_74, plain, (v3_pre_topc(esk3_3(X1,X2,X3),X1)|X3=k2_pre_topc(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  fof(c_0_75, plain, ![X45, X46]:((~v1_tops_1(X46,X45)|k2_pre_topc(X45,X46)=k2_struct_0(X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))&(k2_pre_topc(X45,X46)!=k2_struct_0(X45)|v1_tops_1(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.20/0.42  cnf(c_0_76, plain, (~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X3,k2_pre_topc(X2,X4))|~r2_hidden(X3,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_xboole_0(X4,X1)), inference(csr,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.42  cnf(c_0_77, plain, (r1_xboole_0(X1,X2)|k1_setfam_1(k2_tarski(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_25])).
% 0.20/0.42  cnf(c_0_78, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_65])).
% 0.20/0.42  cnf(c_0_79, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.42  cnf(c_0_80, plain, (v4_pre_topc(k1_xboole_0,X1)|~v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_54]), c_0_68])).
% 0.20/0.42  cnf(c_0_81, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk5_0)), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.42  fof(c_0_82, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|(~r2_hidden(X20,X19)|r2_hidden(X20,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.42  cnf(c_0_83, plain, (r2_hidden(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3))|X3=k2_pre_topc(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_84, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_61]), c_0_72])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_86, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|r1_xboole_0(X2,esk3_3(X1,X2,u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_61]), c_0_72])).
% 0.20/0.42  cnf(c_0_87, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|v3_pre_topc(esk3_3(X1,X2,u1_struct_0(X1)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_61]), c_0_72])).
% 0.20/0.42  cnf(c_0_88, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.42  cnf(c_0_89, plain, (~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X3,k2_pre_topc(X2,k1_xboole_0))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_76, c_0_54])).
% 0.20/0.42  cnf(c_0_90, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.42  cnf(c_0_91, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_79, c_0_54])).
% 0.20/0.42  cnf(c_0_92, negated_conjecture, (v4_pre_topc(k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_58])])).
% 0.20/0.42  cnf(c_0_93, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.42  cnf(c_0_94, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|r2_hidden(esk2_3(X1,X2,u1_struct_0(X1)),esk3_3(X1,X2,u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_61]), c_0_72])).
% 0.20/0.42  cnf(c_0_95, negated_conjecture, (v1_tops_1(esk6_0,esk5_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_pre_topc(X1,esk5_0)|~r1_xboole_0(esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_96, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|m1_subset_1(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_58])])).
% 0.20/0.42  cnf(c_0_97, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|r1_xboole_0(esk6_0,esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_85]), c_0_58])])).
% 0.20/0.42  cnf(c_0_98, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|v3_pre_topc(esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_85]), c_0_58])])).
% 0.20/0.42  cnf(c_0_99, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|~v1_tops_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_85]), c_0_70]), c_0_58])])).
% 0.20/0.42  cnf(c_0_100, plain, (~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X3,k2_pre_topc(X2,k1_xboole_0))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])])).
% 0.20/0.42  cnf(c_0_101, negated_conjecture, (k2_pre_topc(esk5_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_58])])).
% 0.20/0.42  cnf(c_0_102, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_54])).
% 0.20/0.42  cnf(c_0_103, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.42  cnf(c_0_104, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|r2_hidden(esk2_3(esk5_0,esk6_0,u1_struct_0(esk5_0)),esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_85]), c_0_58])])).
% 0.20/0.42  cnf(c_0_105, negated_conjecture, (esk3_3(esk5_0,esk6_0,u1_struct_0(esk5_0))=k1_xboole_0|k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97]), c_0_98]), c_0_99])).
% 0.20/0.42  cnf(c_0_106, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_96]), c_0_58]), c_0_101])]), c_0_102]), c_0_98])).
% 0.20/0.42  cnf(c_0_107, negated_conjecture, (v1_tops_1(X1,esk5_0)|k2_pre_topc(esk5_0,X1)!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_70]), c_0_58])])).
% 0.20/0.42  cnf(c_0_108, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=u1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106])).
% 0.20/0.42  cnf(c_0_109, negated_conjecture, (~v3_pre_topc(X1,esk5_0)|~r2_hidden(X2,k2_pre_topc(esk5_0,esk6_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_85]), c_0_58])])).
% 0.20/0.42  cnf(c_0_110, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_111, negated_conjecture, (v1_tops_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_85])])).
% 0.20/0.42  cnf(c_0_112, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_113, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_114, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k2_pre_topc(X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X4,X1)|~r2_hidden(esk2_3(X1,X2,X3),X4)|~r1_xboole_0(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_115, negated_conjecture, (~v3_pre_topc(X1,esk5_0)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(esk6_0,X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_108]), c_0_93])).
% 0.20/0.42  cnf(c_0_116, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111])])).
% 0.20/0.42  cnf(c_0_117, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_111])])).
% 0.20/0.42  cnf(c_0_118, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_111])])).
% 0.20/0.42  cnf(c_0_119, plain, (X1=k2_pre_topc(X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|~v3_pre_topc(u1_struct_0(X2),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_xboole_0(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_61]), c_0_60])).
% 0.20/0.42  cnf(c_0_120, negated_conjecture, (~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_118])])).
% 0.20/0.42  cnf(c_0_121, negated_conjecture, (esk7_0!=k1_xboole_0|~v1_tops_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_122, negated_conjecture, (k2_pre_topc(esk5_0,X1)=esk7_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_xboole_0(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_116]), c_0_81]), c_0_58])]), c_0_120])).
% 0.20/0.42  cnf(c_0_123, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_111])])).
% 0.20/0.42  cnf(c_0_124, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_54]), c_0_101]), c_0_90])]), c_0_123]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 125
% 0.20/0.42  # Proof object clause steps            : 82
% 0.20/0.42  # Proof object formula steps           : 43
% 0.20/0.42  # Proof object conjectures             : 35
% 0.20/0.42  # Proof object clause conjectures      : 32
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 34
% 0.20/0.42  # Proof object initial formulas used   : 21
% 0.20/0.42  # Proof object generating inferences   : 32
% 0.20/0.42  # Proof object simplifying inferences  : 74
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 21
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 47
% 0.20/0.42  # Removed in clause preprocessing      : 3
% 0.20/0.42  # Initial clauses in saturation        : 44
% 0.20/0.42  # Processed clauses                    : 447
% 0.20/0.42  # ...of these trivial                  : 3
% 0.20/0.42  # ...subsumed                          : 75
% 0.20/0.42  # ...remaining for further processing  : 369
% 0.20/0.42  # Other redundant clauses eliminated   : 5
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 22
% 0.20/0.42  # Backward-rewritten                   : 72
% 0.20/0.42  # Generated clauses                    : 590
% 0.20/0.42  # ...of the previous two non-trivial   : 598
% 0.20/0.42  # Contextual simplify-reflections      : 30
% 0.20/0.42  # Paramodulations                      : 585
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 5
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 227
% 0.20/0.42  #    Positive orientable unit clauses  : 29
% 0.20/0.42  #    Positive unorientable unit clauses: 1
% 0.20/0.42  #    Negative unit clauses             : 4
% 0.20/0.42  #    Non-unit-clauses                  : 193
% 0.20/0.42  # Current number of unprocessed clauses: 220
% 0.20/0.42  # ...number of literals in the above   : 934
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 140
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 9626
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 3583
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 100
% 0.20/0.42  # Unit Clause-clause subsumption calls : 449
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 22
% 0.20/0.42  # BW rewrite match successes           : 14
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 20872
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.072 s
% 0.20/0.42  # System time              : 0.002 s
% 0.20/0.42  # Total time               : 0.074 s
% 0.20/0.42  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
