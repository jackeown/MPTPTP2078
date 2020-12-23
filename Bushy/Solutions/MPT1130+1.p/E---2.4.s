%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : pre_topc__t61_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:45 EDT 2019

% Result     : Theorem 174.44s
% Output     : CNFRefutation 174.44s
% Verified   : 
% Statistics : Number of formulae       :  116 (1630 expanded)
%              Number of clauses        :   79 ( 726 expanded)
%              Number of leaves         :   18 ( 430 expanded)
%              Depth                    :   19
%              Number of atoms          :  373 (5402 expanded)
%              Number of equality atoms :   35 ( 874 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',free_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',abstractness_v1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',dt_u1_pre_topc)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',dt_k2_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',d3_struct_0)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',d6_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',dt_l1_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',t4_subset)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',dt_g1_pre_topc)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',redefinition_k7_subset_1)).

fof(t61_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v4_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',t61_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',d5_pre_topc)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',fc6_pre_topc)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',existence_m1_subset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',t1_subset)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',dt_k7_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t61_pre_topc.p',t2_subset)).

fof(c_0_18,plain,(
    ! [X27,X28,X29,X30] :
      ( ( X27 = X29
        | g1_pre_topc(X27,X28) != g1_pre_topc(X29,X30)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))) )
      & ( X28 = X30
        | g1_pre_topc(X27,X28) != g1_pre_topc(X29,X30)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_19,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | ~ v1_pre_topc(X7)
      | X7 = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_20,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | m1_subset_1(u1_pre_topc(X22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_21,plain,(
    ! [X17] :
      ( ~ l1_struct_0(X17)
      | m1_subset_1(k2_struct_0(X17),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_22,plain,(
    ! [X10] :
      ( ~ l1_struct_0(X10)
      | k2_struct_0(X10) = u1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ( ~ v4_pre_topc(X14,X13)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X13),k2_struct_0(X13),X14),X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X13),k2_struct_0(X13),X14),X13)
        | v4_pre_topc(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

fof(c_0_27,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_28,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_31,plain,(
    ! [X42,X43,X44] :
      ( ~ r2_hidden(X42,X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(X44))
      | m1_subset_1(X42,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_32,plain,
    ( u1_pre_topc(X1) = X2
    | X1 != g1_pre_topc(X3,X2)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_33,plain,(
    ! [X15,X16] :
      ( ( v1_pre_topc(g1_pre_topc(X15,X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( l1_pre_topc(g1_pre_topc(X15,X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_34,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k7_subset_1(X31,X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_37,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( u1_struct_0(X1) = X2
    | X1 != g1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_25])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X2
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v4_pre_topc(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          <=> ( v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_pre_topc])).

cnf(c_0_44,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X2),u1_struct_0(X2),X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_35])).

cnf(c_0_45,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_47,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X11,X12] :
      ( ( ~ v3_pre_topc(X12,X11)
        | r2_hidden(X12,u1_pre_topc(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( ~ r2_hidden(X12,u1_pre_topc(X11))
        | v3_pre_topc(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_50,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

fof(c_0_51,plain,(
    ! [X53] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53)))
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X53),u1_pre_topc(X53)))
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

fof(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      | ~ v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) )
    & ( v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | v4_pre_topc(esk2_0,esk1_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | v4_pre_topc(esk2_0,esk1_0) )
    & ( v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])])).

cnf(c_0_53,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(X2),X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_54,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_42])).

cnf(c_0_55,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X2,X3))))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_42])).

fof(c_0_57,plain,(
    ! [X25] : m1_subset_1(esk5_1(X25),X25) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_58,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( v4_pre_topc(X1,g1_pre_topc(X2,X3))
    | ~ v3_pre_topc(k4_xboole_0(X2,X1),g1_pre_topc(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_42])).

cnf(c_0_61,plain,
    ( v3_pre_topc(X1,g1_pre_topc(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_42]),c_0_56])).

cnf(c_0_62,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_54]),c_0_42])).

cnf(c_0_64,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_58])).

fof(c_0_66,plain,(
    ! [X34,X35] :
      ( ~ r2_hidden(X34,X35)
      | m1_subset_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_67,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | m1_subset_1(k7_subset_1(X18,X19,X20),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_70,plain,
    ( v4_pre_topc(X1,g1_pre_topc(X2,X3))
    | ~ r2_hidden(k4_xboole_0(X2,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_72,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_29]),c_0_35])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_74,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_65]),c_0_58])).

cnf(c_0_75,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_65])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_25]),c_0_69])])).

cnf(c_0_80,plain,
    ( v4_pre_topc(X1,g1_pre_topc(X2,u1_pre_topc(X3)))
    | ~ v3_pre_topc(k4_xboole_0(X2,X1),X3)
    | ~ m1_subset_1(k4_xboole_0(X2,X1),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(u1_pre_topc(X3),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_81,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_45]),c_0_73])])).

cnf(c_0_82,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_74]),c_0_75])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_71])).

cnf(c_0_84,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_45])).

cnf(c_0_85,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_45])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_87,plain,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_25])).

cnf(c_0_88,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_42]),c_0_25])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_65])).

cnf(c_0_90,plain,
    ( v3_pre_topc(k4_xboole_0(X1,X2),g1_pre_topc(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v4_pre_topc(X2,g1_pre_topc(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_54]),c_0_42])).

cnf(c_0_91,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_79]),c_0_69])])).

cnf(c_0_93,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_95,plain,
    ( r2_hidden(k4_xboole_0(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_42]),c_0_25])).

cnf(c_0_96,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),X2),u1_pre_topc(X1))
    | ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_65])).

cnf(c_0_97,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_79]),c_0_69]),c_0_94])])).

fof(c_0_98,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | ~ v1_xboole_0(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_99,plain,
    ( r2_hidden(k4_xboole_0(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_85])).

cnf(c_0_100,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),X2),u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_29]),c_0_73])]),c_0_35])).

cnf(c_0_101,negated_conjecture,
    ( v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_102,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_85]),c_0_73])])).

cnf(c_0_103,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_104,plain,
    ( r2_hidden(k4_xboole_0(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_93]),c_0_73])])).

fof(c_0_105,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X36,X37)
      | v1_xboole_0(X37)
      | r2_hidden(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_106,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_54]),c_0_42]),c_0_25])).

cnf(c_0_107,negated_conjecture,
    ( v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(sr,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,plain,
    ( ~ v1_xboole_0(u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_79]),c_0_69]),c_0_94])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_107]),c_0_79]),c_0_69]),c_0_94])])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])).

cnf(c_0_113,negated_conjecture,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_112]),c_0_69])])).

cnf(c_0_114,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_113]),c_0_79]),c_0_69])]),c_0_102])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_85]),c_0_73])]),
    [proof]).
%------------------------------------------------------------------------------
