%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:34 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 376 expanded)
%              Number of clauses        :   70 ( 164 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  338 (1314 expanded)
%              Number of equality atoms :   41 ( 239 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t28_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r2_hidden(X4,X3)
                      <=> ( v3_pre_topc(X4,X1)
                          & v4_pre_topc(X4,X1)
                          & r2_hidden(X2,X4) ) ) )
                  & X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(cc2_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(cc1_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(rc3_tops_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v3_pre_topc(X2,X1)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_21,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r1_xboole_0(X8,X9)
        | r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_23,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X17] : k3_xboole_0(X17,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X4,X3)
                        <=> ( v3_pre_topc(X4,X1)
                            & v4_pre_topc(X4,X1)
                            & r2_hidden(X2,X4) ) ) )
                    & X3 = k1_xboole_0 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_connsp_2])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_25])).

fof(c_0_37,plain,(
    ! [X30] :
      ( ( r1_xboole_0(X30,X30)
        | X30 != k1_xboole_0 )
      & ( X30 = k1_xboole_0
        | ~ r1_xboole_0(X30,X30) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_38,negated_conjecture,(
    ! [X73] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & l1_pre_topc(esk5_0)
      & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
      & ( v3_pre_topc(X73,esk5_0)
        | ~ r2_hidden(X73,esk7_0)
        | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(esk5_0))) )
      & ( v4_pre_topc(X73,esk5_0)
        | ~ r2_hidden(X73,esk7_0)
        | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(esk5_0))) )
      & ( r2_hidden(esk6_0,X73)
        | ~ r2_hidden(X73,esk7_0)
        | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(esk5_0))) )
      & ( ~ v3_pre_topc(X73,esk5_0)
        | ~ v4_pre_topc(X73,esk5_0)
        | ~ r2_hidden(esk6_0,X73)
        | r2_hidden(X73,esk7_0)
        | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(esk5_0))) )
      & esk7_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_34])])])])])])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_41,plain,(
    ! [X60,X61] :
      ( ~ v2_pre_topc(X60)
      | ~ l1_pre_topc(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
      | ~ v1_xboole_0(X61)
      | v4_pre_topc(X61,X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X66,X67] :
      ( ( ~ v4_pre_topc(X67,X66)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X66),X67),X66)
        | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
        | ~ l1_pre_topc(X66) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X66),X67),X66)
        | v4_pre_topc(X67,X66)
        | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
        | ~ l1_pre_topc(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_36])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_47,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | m1_subset_1(k3_subset_1(X38,X39),k1_zfmisc_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_48,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | k3_subset_1(X36,X37) = k4_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_49,plain,(
    ! [X62,X63] :
      ( ~ v2_pre_topc(X62)
      | ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | ~ v1_xboole_0(X63)
      | v3_pre_topc(X63,X62) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).

fof(c_0_50,plain,(
    ! [X31] :
      ( ~ v1_xboole_0(X31)
      | X31 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_51,plain,(
    ! [X40] :
      ( m1_subset_1(esk2_1(X40),k1_zfmisc_1(X40))
      & v1_xboole_0(esk2_1(X40)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

fof(c_0_52,plain,(
    ! [X68,X69] :
      ( ( ~ v3_pre_topc(X69,X68)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X68),X69),X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ l1_pre_topc(X68) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X68),X69),X68)
        | v3_pre_topc(X69,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ l1_pre_topc(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_53,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_57,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_59,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_60,plain,(
    ! [X25,X26,X27] : k4_xboole_0(X25,k4_xboole_0(X26,X27)) = k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_61,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k3_xboole_0(X18,X19)) = k4_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_62,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_63,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,plain,
    ( v1_xboole_0(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(esk5_0),X1),esk5_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(esk6_0,k3_subset_1(u1_struct_0(esk5_0),X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_55])]),c_0_58]),c_0_59])).

cnf(c_0_70,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_71,plain,(
    ! [X43,X44] :
      ( ~ v1_xboole_0(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | v1_xboole_0(X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_72,plain,(
    ! [X64] :
      ( ( m1_subset_1(esk4_1(X64),k1_zfmisc_1(u1_struct_0(X64)))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) )
      & ( ~ v1_xboole_0(esk4_1(X64))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) )
      & ( v3_pre_topc(esk4_1(X64),X64)
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) )
      & ( v4_pre_topc(esk4_1(X64),X64)
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_tops_1])])])])])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_75,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_54]),c_0_55])])).

cnf(c_0_77,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_63])).

cnf(c_0_78,plain,
    ( esk2_1(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(k3_subset_1(u1_struct_0(esk5_0),X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_55])]),c_0_59])).

cnf(c_0_80,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk5_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(esk6_0,k3_subset_1(u1_struct_0(esk5_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_55])])).

fof(c_0_81,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X35,X34)
        | r2_hidden(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ r2_hidden(X35,X34)
        | m1_subset_1(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ m1_subset_1(X35,X34)
        | v1_xboole_0(X35)
        | ~ v1_xboole_0(X34) )
      & ( ~ v1_xboole_0(X35)
        | m1_subset_1(X35,X34)
        | ~ v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_82,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,plain,
    ( m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk4_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_25])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_74,c_0_25])).

fof(c_0_87,plain,(
    ! [X14] : k2_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_88,negated_conjecture,
    ( v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(k4_xboole_0(u1_struct_0(esk5_0),X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_55])]),c_0_77])).

cnf(c_0_89,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_78])).

fof(c_0_90,plain,(
    ! [X42] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X42)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_91,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(k4_xboole_0(u1_struct_0(esk5_0),X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_63])).

cnf(c_0_92,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk5_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(esk6_0,k4_xboole_0(u1_struct_0(esk5_0),X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_63])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_96,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_97,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_98,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_99,negated_conjecture,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),esk5_0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_36]),c_0_89])])).

cnf(c_0_100,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_101,negated_conjecture,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),esk5_0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_36]),c_0_89])])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(esk5_0),X1))
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(esk6_0,k4_xboole_0(u1_struct_0(esk5_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_104,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_55]),c_0_54])])).

cnf(c_0_105,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_36]),c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( v3_pre_topc(k1_xboole_0,esk5_0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_55]),c_0_100])])).

cnf(c_0_107,negated_conjecture,
    ( v4_pre_topc(k1_xboole_0,esk5_0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_101]),c_0_55]),c_0_100])])).

cnf(c_0_108,negated_conjecture,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),esk5_0)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),esk5_0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_28]),c_0_103])]),c_0_104])).

cnf(c_0_109,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( v3_pre_topc(k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_77]),c_0_100])])).

cnf(c_0_111,negated_conjecture,
    ( v4_pre_topc(k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_77]),c_0_100])])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109]),c_0_110]),c_0_109]),c_0_111]),c_0_109]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:09:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.65/0.82  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.65/0.82  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.65/0.82  #
% 0.65/0.82  # Preprocessing time       : 0.029 s
% 0.65/0.82  
% 0.65/0.82  # Proof found!
% 0.65/0.82  # SZS status Theorem
% 0.65/0.82  # SZS output start CNFRefutation
% 0.65/0.82  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.65/0.82  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.65/0.82  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.65/0.82  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.65/0.82  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.65/0.82  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.65/0.82  fof(cc2_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 0.65/0.82  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 0.65/0.82  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.65/0.82  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.65/0.82  fof(cc1_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 0.65/0.82  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 0.65/0.82  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.65/0.82  fof(t30_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 0.65/0.82  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.65/0.82  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.65/0.82  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.65/0.82  fof(rc3_tops_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:(((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v3_pre_topc(X2,X1))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 0.65/0.82  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.65/0.82  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.65/0.82  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.65/0.82  fof(c_0_21, plain, ![X8, X9, X11, X12, X13]:((r1_xboole_0(X8,X9)|r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)))&(~r2_hidden(X13,k3_xboole_0(X11,X12))|~r1_xboole_0(X11,X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.65/0.82  fof(c_0_22, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.65/0.82  fof(c_0_23, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.65/0.82  cnf(c_0_24, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.65/0.82  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.65/0.82  cnf(c_0_26, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.65/0.82  cnf(c_0_27, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.65/0.82  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 0.65/0.82  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.65/0.82  fof(c_0_30, plain, ![X17]:k3_xboole_0(X17,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.65/0.82  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.65/0.82  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_29, c_0_25])).
% 0.65/0.82  cnf(c_0_33, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.65/0.82  fof(c_0_34, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.65/0.82  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.65/0.82  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_33, c_0_25])).
% 0.65/0.82  fof(c_0_37, plain, ![X30]:((r1_xboole_0(X30,X30)|X30!=k1_xboole_0)&(X30=k1_xboole_0|~r1_xboole_0(X30,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.65/0.82  fof(c_0_38, negated_conjecture, ![X73]:(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))&(((((v3_pre_topc(X73,esk5_0)|~r2_hidden(X73,esk7_0)|~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(esk5_0))))&(v4_pre_topc(X73,esk5_0)|~r2_hidden(X73,esk7_0)|~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(esk5_0)))))&(r2_hidden(esk6_0,X73)|~r2_hidden(X73,esk7_0)|~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(esk5_0)))))&(~v3_pre_topc(X73,esk5_0)|~v4_pre_topc(X73,esk5_0)|~r2_hidden(esk6_0,X73)|r2_hidden(X73,esk7_0)|~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(esk5_0)))))&esk7_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_34])])])])])])).
% 0.65/0.82  cnf(c_0_39, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.65/0.82  cnf(c_0_40, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.65/0.82  fof(c_0_41, plain, ![X60, X61]:(~v2_pre_topc(X60)|~l1_pre_topc(X60)|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|(~v1_xboole_0(X61)|v4_pre_topc(X61,X60)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).
% 0.65/0.82  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,esk7_0)|~v3_pre_topc(X1,esk5_0)|~v4_pre_topc(X1,esk5_0)|~r2_hidden(esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.65/0.82  cnf(c_0_43, negated_conjecture, (esk7_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.65/0.82  fof(c_0_44, plain, ![X66, X67]:((~v4_pre_topc(X67,X66)|v3_pre_topc(k3_subset_1(u1_struct_0(X66),X67),X66)|~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|~l1_pre_topc(X66))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X66),X67),X66)|v4_pre_topc(X67,X66)|~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|~l1_pre_topc(X66))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.65/0.82  cnf(c_0_45, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_36])).
% 0.65/0.82  cnf(c_0_46, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.65/0.82  fof(c_0_47, plain, ![X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|m1_subset_1(k3_subset_1(X38,X39),k1_zfmisc_1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.65/0.82  fof(c_0_48, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|k3_subset_1(X36,X37)=k4_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.65/0.82  fof(c_0_49, plain, ![X62, X63]:(~v2_pre_topc(X62)|~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|(~v1_xboole_0(X63)|v3_pre_topc(X63,X62)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).
% 0.65/0.82  fof(c_0_50, plain, ![X31]:(~v1_xboole_0(X31)|X31=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.65/0.82  fof(c_0_51, plain, ![X40]:(m1_subset_1(esk2_1(X40),k1_zfmisc_1(X40))&v1_xboole_0(esk2_1(X40))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.65/0.82  fof(c_0_52, plain, ![X68, X69]:((~v3_pre_topc(X69,X68)|v4_pre_topc(k3_subset_1(u1_struct_0(X68),X69),X68)|~m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))|~l1_pre_topc(X68))&(~v4_pre_topc(k3_subset_1(u1_struct_0(X68),X69),X68)|v3_pre_topc(X69,X68)|~m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))|~l1_pre_topc(X68))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).
% 0.65/0.82  cnf(c_0_53, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.65/0.82  cnf(c_0_54, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.65/0.82  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.65/0.82  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v3_pre_topc(X1,esk5_0)|~v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(esk6_0,X1)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.65/0.82  cnf(c_0_57, plain, (v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.65/0.82  cnf(c_0_58, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.65/0.82  cnf(c_0_59, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.65/0.82  fof(c_0_60, plain, ![X25, X26, X27]:k4_xboole_0(X25,k4_xboole_0(X26,X27))=k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.65/0.82  fof(c_0_61, plain, ![X18, X19]:k4_xboole_0(X18,k3_xboole_0(X18,X19))=k4_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.65/0.82  cnf(c_0_62, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.65/0.82  cnf(c_0_63, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.65/0.82  cnf(c_0_64, plain, (v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.65/0.82  cnf(c_0_65, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.65/0.82  cnf(c_0_66, plain, (v1_xboole_0(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.65/0.82  cnf(c_0_67, plain, (v3_pre_topc(X2,X1)|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.65/0.82  cnf(c_0_68, negated_conjecture, (v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.65/0.82  cnf(c_0_69, negated_conjecture, (~v4_pre_topc(k3_subset_1(u1_struct_0(esk5_0),X1),esk5_0)|~v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(esk6_0,k3_subset_1(u1_struct_0(esk5_0),X1))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_55])]), c_0_58]), c_0_59])).
% 0.65/0.82  cnf(c_0_70, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.65/0.82  fof(c_0_71, plain, ![X43, X44]:(~v1_xboole_0(X43)|(~m1_subset_1(X44,k1_zfmisc_1(X43))|v1_xboole_0(X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.65/0.82  fof(c_0_72, plain, ![X64]:((((m1_subset_1(esk4_1(X64),k1_zfmisc_1(u1_struct_0(X64)))|(v2_struct_0(X64)|~v2_pre_topc(X64)|~l1_pre_topc(X64)))&(~v1_xboole_0(esk4_1(X64))|(v2_struct_0(X64)|~v2_pre_topc(X64)|~l1_pre_topc(X64))))&(v3_pre_topc(esk4_1(X64),X64)|(v2_struct_0(X64)|~v2_pre_topc(X64)|~l1_pre_topc(X64))))&(v4_pre_topc(esk4_1(X64),X64)|(v2_struct_0(X64)|~v2_pre_topc(X64)|~l1_pre_topc(X64)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_tops_1])])])])])).
% 0.65/0.82  cnf(c_0_73, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.65/0.82  cnf(c_0_74, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.65/0.82  cnf(c_0_75, plain, (v4_pre_topc(X1,X2)|~v3_pre_topc(k4_xboole_0(u1_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.65/0.82  cnf(c_0_76, negated_conjecture, (v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_54]), c_0_55])])).
% 0.65/0.82  cnf(c_0_77, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_63])).
% 0.65/0.82  cnf(c_0_78, plain, (esk2_1(X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.65/0.82  cnf(c_0_79, negated_conjecture, (v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(k3_subset_1(u1_struct_0(esk5_0),X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_55])]), c_0_59])).
% 0.65/0.82  cnf(c_0_80, negated_conjecture, (~v3_pre_topc(X1,esk5_0)|~v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(esk6_0,k3_subset_1(u1_struct_0(esk5_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_55])])).
% 0.65/0.82  fof(c_0_81, plain, ![X34, X35]:(((~m1_subset_1(X35,X34)|r2_hidden(X35,X34)|v1_xboole_0(X34))&(~r2_hidden(X35,X34)|m1_subset_1(X35,X34)|v1_xboole_0(X34)))&((~m1_subset_1(X35,X34)|v1_xboole_0(X35)|~v1_xboole_0(X34))&(~v1_xboole_0(X35)|m1_subset_1(X35,X34)|~v1_xboole_0(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.65/0.82  cnf(c_0_82, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.65/0.82  cnf(c_0_83, plain, (m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.65/0.82  cnf(c_0_84, plain, (v2_struct_0(X1)|~v1_xboole_0(esk4_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.65/0.82  cnf(c_0_85, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_73, c_0_25])).
% 0.65/0.82  cnf(c_0_86, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_74, c_0_25])).
% 0.65/0.82  fof(c_0_87, plain, ![X14]:k2_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.65/0.82  cnf(c_0_88, negated_conjecture, (v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(k4_xboole_0(u1_struct_0(esk5_0),X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_55])]), c_0_77])).
% 0.65/0.82  cnf(c_0_89, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_66, c_0_78])).
% 0.65/0.82  fof(c_0_90, plain, ![X42]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X42)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.65/0.82  cnf(c_0_91, negated_conjecture, (v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(k4_xboole_0(u1_struct_0(esk5_0),X1))), inference(spm,[status(thm)],[c_0_79, c_0_63])).
% 0.65/0.82  cnf(c_0_92, negated_conjecture, (~v3_pre_topc(X1,esk5_0)|~v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(esk6_0,k4_xboole_0(u1_struct_0(esk5_0),X1))), inference(spm,[status(thm)],[c_0_80, c_0_63])).
% 0.65/0.82  cnf(c_0_93, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.65/0.82  cnf(c_0_94, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.65/0.82  cnf(c_0_95, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.65/0.82  cnf(c_0_96, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.65/0.82  cnf(c_0_97, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.65/0.82  cnf(c_0_98, plain, (v3_pre_topc(X1,X2)|~v4_pre_topc(k4_xboole_0(u1_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 0.65/0.82  cnf(c_0_99, negated_conjecture, (v4_pre_topc(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),esk5_0)|~m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_36]), c_0_89])])).
% 0.65/0.82  cnf(c_0_100, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.65/0.82  cnf(c_0_101, negated_conjecture, (v3_pre_topc(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),esk5_0)|~m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_36]), c_0_89])])).
% 0.65/0.82  cnf(c_0_102, negated_conjecture, (v1_xboole_0(k4_xboole_0(u1_struct_0(esk5_0),X1))|~v3_pre_topc(X1,esk5_0)|~v4_pre_topc(X1,esk5_0)|~m1_subset_1(esk6_0,k4_xboole_0(u1_struct_0(esk5_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.65/0.82  cnf(c_0_103, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.65/0.82  cnf(c_0_104, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_55]), c_0_54])])).
% 0.65/0.82  cnf(c_0_105, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_36]), c_0_97])).
% 0.65/0.82  cnf(c_0_106, negated_conjecture, (v3_pre_topc(k1_xboole_0,esk5_0)|~m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_55]), c_0_100])])).
% 0.65/0.82  cnf(c_0_107, negated_conjecture, (v4_pre_topc(k1_xboole_0,esk5_0)|~m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_101]), c_0_55]), c_0_100])])).
% 0.65/0.82  cnf(c_0_108, negated_conjecture, (~v3_pre_topc(k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),esk5_0)|~v4_pre_topc(k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),esk5_0)|~m1_subset_1(k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_28]), c_0_103])]), c_0_104])).
% 0.65/0.82  cnf(c_0_109, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_105])).
% 0.65/0.82  cnf(c_0_110, negated_conjecture, (v3_pre_topc(k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_77]), c_0_100])])).
% 0.65/0.82  cnf(c_0_111, negated_conjecture, (v4_pre_topc(k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_77]), c_0_100])])).
% 0.65/0.82  cnf(c_0_112, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109]), c_0_110]), c_0_109]), c_0_111]), c_0_109]), c_0_100])]), ['proof']).
% 0.65/0.82  # SZS output end CNFRefutation
% 0.65/0.82  # Proof object total steps             : 113
% 0.65/0.82  # Proof object clause steps            : 70
% 0.65/0.82  # Proof object formula steps           : 43
% 0.65/0.82  # Proof object conjectures             : 28
% 0.65/0.82  # Proof object clause conjectures      : 25
% 0.65/0.82  # Proof object formula conjectures     : 3
% 0.65/0.82  # Proof object initial clauses used    : 30
% 0.65/0.82  # Proof object initial formulas used   : 21
% 0.65/0.82  # Proof object generating inferences   : 29
% 0.65/0.82  # Proof object simplifying inferences  : 56
% 0.65/0.82  # Training examples: 0 positive, 0 negative
% 0.65/0.82  # Parsed axioms                        : 32
% 0.65/0.82  # Removed by relevancy pruning/SinE    : 0
% 0.65/0.82  # Initial clauses                      : 56
% 0.65/0.82  # Removed in clause preprocessing      : 1
% 0.65/0.82  # Initial clauses in saturation        : 55
% 0.65/0.82  # Processed clauses                    : 1888
% 0.65/0.82  # ...of these trivial                  : 51
% 0.65/0.82  # ...subsumed                          : 1274
% 0.65/0.82  # ...remaining for further processing  : 563
% 0.65/0.82  # Other redundant clauses eliminated   : 0
% 0.65/0.82  # Clauses deleted for lack of memory   : 0
% 0.65/0.82  # Backward-subsumed                    : 59
% 0.65/0.82  # Backward-rewritten                   : 100
% 0.65/0.82  # Generated clauses                    : 29046
% 0.65/0.82  # ...of the previous two non-trivial   : 24782
% 0.65/0.82  # Contextual simplify-reflections      : 17
% 0.65/0.82  # Paramodulations                      : 29046
% 0.65/0.82  # Factorizations                       : 0
% 0.65/0.82  # Equation resolutions                 : 0
% 0.65/0.82  # Propositional unsat checks           : 0
% 0.65/0.82  #    Propositional check models        : 0
% 0.65/0.82  #    Propositional check unsatisfiable : 0
% 0.65/0.82  #    Propositional clauses             : 0
% 0.65/0.82  #    Propositional clauses after purity: 0
% 0.65/0.82  #    Propositional unsat core size     : 0
% 0.65/0.82  #    Propositional preprocessing time  : 0.000
% 0.65/0.82  #    Propositional encoding time       : 0.000
% 0.65/0.82  #    Propositional solver time         : 0.000
% 0.65/0.82  #    Success case prop preproc time    : 0.000
% 0.65/0.82  #    Success case prop encoding time   : 0.000
% 0.65/0.82  #    Success case prop solver time     : 0.000
% 0.65/0.82  # Current number of processed clauses  : 404
% 0.65/0.82  #    Positive orientable unit clauses  : 70
% 0.65/0.82  #    Positive unorientable unit clauses: 2
% 0.65/0.82  #    Negative unit clauses             : 9
% 0.65/0.82  #    Non-unit-clauses                  : 323
% 0.65/0.82  # Current number of unprocessed clauses: 22234
% 0.65/0.82  # ...number of literals in the above   : 50581
% 0.65/0.82  # Current number of archived formulas  : 0
% 0.65/0.82  # Current number of archived clauses   : 160
% 0.65/0.82  # Clause-clause subsumption calls (NU) : 21462
% 0.65/0.82  # Rec. Clause-clause subsumption calls : 11500
% 0.65/0.82  # Non-unit clause-clause subsumptions  : 775
% 0.65/0.82  # Unit Clause-clause subsumption calls : 610
% 0.65/0.82  # Rewrite failures with RHS unbound    : 0
% 0.65/0.82  # BW rewrite match attempts            : 1760
% 0.65/0.82  # BW rewrite match successes           : 75
% 0.65/0.82  # Condensation attempts                : 0
% 0.65/0.82  # Condensation successes               : 0
% 0.65/0.82  # Termbank termtop insertions          : 708688
% 0.65/0.82  
% 0.65/0.82  # -------------------------------------------------
% 0.65/0.82  # User time                : 0.465 s
% 0.65/0.82  # System time              : 0.027 s
% 0.65/0.82  # Total time               : 0.492 s
% 0.65/0.82  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
