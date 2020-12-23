%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:32 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   96 (1092 expanded)
%              Number of clauses        :   57 ( 421 expanded)
%              Number of leaves         :   19 ( 268 expanded)
%              Depth                    :   12
%              Number of atoms          :  308 (5029 expanded)
%              Number of equality atoms :   41 ( 260 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(rc4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_tops_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_tops_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t47_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v3_tex_2(X2,X1) )
           => v1_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t43_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(t48_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v1_tops_1(X2,X1)
              & v2_tex_2(X2,X1) )
           => v3_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tex_2(X2,X1)
            <=> ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tex_2])).

fof(c_0_20,plain,(
    ! [X34,X35] :
      ( ( ~ v1_tdlat_3(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | v3_pre_topc(X35,X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk3_1(X34),k1_zfmisc_1(u1_struct_0(X34)))
        | v1_tdlat_3(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ v3_pre_topc(esk3_1(X34),X34)
        | v1_tdlat_3(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_21,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | ~ v1_tdlat_3(X29)
      | v2_pre_topc(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_22,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | r1_tarski(X8,X6)
        | X7 != k1_zfmisc_1(X6) )
      & ( ~ r1_tarski(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k1_zfmisc_1(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | ~ r1_tarski(esk1_2(X10,X11),X10)
        | X11 = k1_zfmisc_1(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(esk1_2(X10,X11),X10)
        | X11 = k1_zfmisc_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_23,plain,(
    ! [X32,X33] :
      ( ( ~ v1_subset_1(X33,X32)
        | X33 != X32
        | ~ m1_subset_1(X33,k1_zfmisc_1(X32)) )
      & ( X33 = X32
        | v1_subset_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & v1_tdlat_3(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v3_tex_2(esk5_0,esk4_0)
      | v1_subset_1(esk5_0,u1_struct_0(esk4_0)) )
    & ( v3_tex_2(esk5_0,esk4_0)
      | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_25,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X27] :
      ( ( m1_subset_1(esk2_1(X27),k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( v1_tops_1(esk2_1(X27),X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc4_tops_1])])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_30,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X30,X31] :
      ( ( ~ v1_tops_1(X31,X30)
        | k2_pre_topc(X30,X31) = u1_struct_0(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( k2_pre_topc(X30,X31) != u1_struct_0(X30)
        | v1_tops_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

cnf(c_0_36,plain,
    ( v1_tops_1(esk2_1(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X14] : m1_subset_1(k2_subset_1(X14),k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_39,plain,(
    ! [X13] : k2_subset_1(X13) = X13 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_40,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | m1_subset_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_43,plain,(
    ! [X39,X40] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | ~ v3_pre_topc(X40,X39)
      | ~ v3_tex_2(X40,X39)
      | v1_tops_1(X40,X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).

cnf(c_0_44,negated_conjecture,
    ( v3_tex_2(esk5_0,esk4_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

fof(c_0_47,plain,(
    ! [X25,X26] :
      ( ( ~ v1_tops_1(X26,X25)
        | k2_pre_topc(X25,X26) = k2_struct_0(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( k2_pre_topc(X25,X26) != k2_struct_0(X25)
        | v1_tops_1(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

cnf(c_0_48,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( v1_tops_1(esk2_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

fof(c_0_51,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k7_subset_1(X15,X16,X17) = k4_xboole_0(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_56,plain,(
    ! [X37,X38] :
      ( v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ v1_tdlat_3(X37)
      | ~ l1_pre_topc(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | v2_tex_2(X38,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | v3_tex_2(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_62,plain,(
    ! [X21,X22] :
      ( ( ~ v4_pre_topc(X22,X21)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X21),k2_struct_0(X21),X22),X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X21),k2_struct_0(X21),X22),X21)
        | v4_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

cnf(c_0_63,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk2_1(esk4_0)) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_34]),c_0_50])])).

cnf(c_0_65,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_67,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_69,plain,(
    ! [X23,X24] :
      ( ( ~ v4_pre_topc(X24,X23)
        | k2_pre_topc(X23,X24) = X24
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( ~ v2_pre_topc(X23)
        | k2_pre_topc(X23,X24) != X24
        | v4_pre_topc(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | v1_tops_1(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_34]),c_0_31])]),c_0_61])).

cnf(c_0_71,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( k2_struct_0(esk4_0) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_49]),c_0_64]),c_0_34]),c_0_50])])).

cnf(c_0_73,plain,
    ( k7_subset_1(X1,X1,X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(esk4_0),X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_67])).

cnf(c_0_75,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_68,c_0_26])).

cnf(c_0_76,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_70]),c_0_34]),c_0_31])])).

cnf(c_0_78,negated_conjecture,
    ( v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_34])]),c_0_73]),c_0_74])])).

fof(c_0_79,plain,(
    ! [X18] : ~ v1_subset_1(k2_subset_1(X18),X18) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

fof(c_0_80,plain,(
    ! [X41,X42] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | ~ v1_tops_1(X42,X41)
      | ~ v2_tex_2(X42,X41)
      | v3_tex_2(X42,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).

cnf(c_0_81,negated_conjecture,
    ( v2_tex_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_33]),c_0_34])]),c_0_61])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | ~ v4_pre_topc(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_34]),c_0_31])])).

cnf(c_0_83,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_31])).

cnf(c_0_84,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_66])).

cnf(c_0_87,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ v3_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_89,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_84,c_0_53])).

cnf(c_0_90,negated_conjecture,
    ( v3_tex_2(u1_struct_0(esk4_0),esk4_0)
    | ~ v1_tops_1(u1_struct_0(esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_59]),c_0_34]),c_0_66])]),c_0_61])).

cnf(c_0_91,negated_conjecture,
    ( ~ v3_tex_2(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_92,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_93,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_83]),c_0_34]),c_0_31])])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_tops_1(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_88]),c_0_88]),c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_88]),c_0_34]),c_0_88]),c_0_66])]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:20:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.14/0.38  # and selection function PSelectComplexPreferEQ.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.030 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t49_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 0.14/0.38  fof(t17_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 0.14/0.38  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.14/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.14/0.38  fof(rc4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v1_tops_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_tops_1)).
% 0.14/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.14/0.38  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 0.14/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.14/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.14/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.14/0.38  fof(t47_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tex_2(X2,X1))=>v1_tops_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 0.14/0.38  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 0.14/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.14/0.38  fof(t43_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 0.14/0.38  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 0.14/0.38  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.14/0.38  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.14/0.38  fof(t48_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_tops_1(X2,X1)&v2_tex_2(X2,X1))=>v3_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 0.14/0.38  fof(c_0_19, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t49_tex_2])).
% 0.14/0.38  fof(c_0_20, plain, ![X34, X35]:((~v1_tdlat_3(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|v3_pre_topc(X35,X34))|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))&((m1_subset_1(esk3_1(X34),k1_zfmisc_1(u1_struct_0(X34)))|v1_tdlat_3(X34)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(~v3_pre_topc(esk3_1(X34),X34)|v1_tdlat_3(X34)|(~v2_pre_topc(X34)|~l1_pre_topc(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).
% 0.14/0.38  fof(c_0_21, plain, ![X29]:(~l1_pre_topc(X29)|(~v1_tdlat_3(X29)|v2_pre_topc(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.14/0.38  fof(c_0_22, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|r1_tarski(X8,X6)|X7!=k1_zfmisc_1(X6))&(~r1_tarski(X9,X6)|r2_hidden(X9,X7)|X7!=k1_zfmisc_1(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|~r1_tarski(esk1_2(X10,X11),X10)|X11=k1_zfmisc_1(X10))&(r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(esk1_2(X10,X11),X10)|X11=k1_zfmisc_1(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.38  fof(c_0_23, plain, ![X32, X33]:((~v1_subset_1(X33,X32)|X33!=X32|~m1_subset_1(X33,k1_zfmisc_1(X32)))&(X33=X32|v1_subset_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.14/0.38  fof(c_0_24, negated_conjecture, ((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v1_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~v3_tex_2(esk5_0,esk4_0)|v1_subset_1(esk5_0,u1_struct_0(esk4_0)))&(v3_tex_2(esk5_0,esk4_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.14/0.38  cnf(c_0_25, plain, (v3_pre_topc(X2,X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_26, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  fof(c_0_27, plain, ![X27]:((m1_subset_1(esk2_1(X27),k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(v1_tops_1(esk2_1(X27),X27)|~l1_pre_topc(X27))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc4_tops_1])])])])).
% 0.14/0.38  cnf(c_0_28, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  fof(c_0_29, plain, ![X4, X5]:r1_tarski(k4_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.14/0.38  cnf(c_0_30, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_32, plain, (v3_pre_topc(X1,X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (v1_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  fof(c_0_35, plain, ![X30, X31]:((~v1_tops_1(X31,X30)|k2_pre_topc(X30,X31)=u1_struct_0(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(k2_pre_topc(X30,X31)!=u1_struct_0(X30)|v1_tops_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.14/0.38  cnf(c_0_36, plain, (v1_tops_1(esk2_1(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_37, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  fof(c_0_38, plain, ![X14]:m1_subset_1(k2_subset_1(X14),k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.14/0.38  fof(c_0_39, plain, ![X13]:k2_subset_1(X13)=X13, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.14/0.38  fof(c_0_40, plain, ![X19, X20]:(~r2_hidden(X19,X20)|m1_subset_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.14/0.38  cnf(c_0_41, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  fof(c_0_43, plain, ![X39, X40]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(~v3_pre_topc(X40,X39)|~v3_tex_2(X40,X39)|v1_tops_1(X40,X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (v3_tex_2(esk5_0,esk4_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.14/0.38  fof(c_0_47, plain, ![X25, X26]:((~v1_tops_1(X26,X25)|k2_pre_topc(X25,X26)=k2_struct_0(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))&(k2_pre_topc(X25,X26)!=k2_struct_0(X25)|v1_tops_1(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.14/0.38  cnf(c_0_48, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (v1_tops_1(esk2_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 0.14/0.38  fof(c_0_51, plain, ![X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|k7_subset_1(X15,X16,X17)=k4_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.14/0.38  cnf(c_0_52, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_53, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.38  cnf(c_0_54, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.38  cnf(c_0_55, plain, (r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.38  fof(c_0_56, plain, ![X37, X38]:(v2_struct_0(X37)|~v2_pre_topc(X37)|~v1_tdlat_3(X37)|~l1_pre_topc(X37)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|v2_tex_2(X38,X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).
% 0.14/0.38  cnf(c_0_57, plain, (v2_struct_0(X1)|v1_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|v3_tex_2(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (v3_pre_topc(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  fof(c_0_62, plain, ![X21, X22]:((~v4_pre_topc(X22,X21)|v3_pre_topc(k7_subset_1(u1_struct_0(X21),k2_struct_0(X21),X22),X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X21),k2_struct_0(X21),X22),X21)|v4_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 0.14/0.38  cnf(c_0_63, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.38  cnf(c_0_64, negated_conjecture, (k2_pre_topc(esk4_0,esk2_1(esk4_0))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_34]), c_0_50])])).
% 0.14/0.38  cnf(c_0_65, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.38  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.14/0.38  cnf(c_0_67, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.38  cnf(c_0_68, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.38  fof(c_0_69, plain, ![X23, X24]:((~v4_pre_topc(X24,X23)|k2_pre_topc(X23,X24)=X24|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(~v2_pre_topc(X23)|k2_pre_topc(X23,X24)!=X24|v4_pre_topc(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.14/0.38  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|v1_tops_1(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), c_0_34]), c_0_31])]), c_0_61])).
% 0.14/0.38  cnf(c_0_71, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, (k2_struct_0(esk4_0)=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_49]), c_0_64]), c_0_34]), c_0_50])])).
% 0.14/0.38  cnf(c_0_73, plain, (k7_subset_1(X1,X1,X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.14/0.38  cnf(c_0_74, negated_conjecture, (v3_pre_topc(k4_xboole_0(u1_struct_0(esk4_0),X1),esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_67])).
% 0.14/0.38  cnf(c_0_75, plain, (v2_tex_2(X1,X2)|v2_struct_0(X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_68, c_0_26])).
% 0.14/0.38  cnf(c_0_76, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.14/0.38  cnf(c_0_77, negated_conjecture, (k2_pre_topc(esk4_0,esk5_0)=u1_struct_0(esk4_0)|u1_struct_0(esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_70]), c_0_34]), c_0_31])])).
% 0.14/0.38  cnf(c_0_78, negated_conjecture, (v4_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_34])]), c_0_73]), c_0_74])])).
% 0.14/0.38  fof(c_0_79, plain, ![X18]:~v1_subset_1(k2_subset_1(X18),X18), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.14/0.38  fof(c_0_80, plain, ![X41, X42]:(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(~v1_tops_1(X42,X41)|~v2_tex_2(X42,X41)|v3_tex_2(X42,X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tex_2])])])])).
% 0.14/0.38  cnf(c_0_81, negated_conjecture, (v2_tex_2(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_33]), c_0_34])]), c_0_61])).
% 0.14/0.38  cnf(c_0_82, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|~v4_pre_topc(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_34]), c_0_31])])).
% 0.14/0.38  cnf(c_0_83, negated_conjecture, (v4_pre_topc(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_78, c_0_31])).
% 0.14/0.38  cnf(c_0_84, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.14/0.38  cnf(c_0_85, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_tops_1(X2,X1)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.14/0.38  cnf(c_0_86, negated_conjecture, (v2_tex_2(u1_struct_0(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_81, c_0_66])).
% 0.14/0.38  cnf(c_0_87, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~v3_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_88, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 0.14/0.38  cnf(c_0_89, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_84, c_0_53])).
% 0.14/0.38  cnf(c_0_90, negated_conjecture, (v3_tex_2(u1_struct_0(esk4_0),esk4_0)|~v1_tops_1(u1_struct_0(esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_59]), c_0_34]), c_0_66])]), c_0_61])).
% 0.14/0.38  cnf(c_0_91, negated_conjecture, (~v3_tex_2(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.14/0.38  cnf(c_0_92, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.38  cnf(c_0_93, negated_conjecture, (k2_pre_topc(esk4_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_83]), c_0_34]), c_0_31])])).
% 0.14/0.38  cnf(c_0_94, negated_conjecture, (~v1_tops_1(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_88]), c_0_88]), c_0_91])).
% 0.14/0.38  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_88]), c_0_34]), c_0_88]), c_0_66])]), c_0_94]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 96
% 0.14/0.38  # Proof object clause steps            : 57
% 0.14/0.38  # Proof object formula steps           : 39
% 0.14/0.38  # Proof object conjectures             : 32
% 0.14/0.38  # Proof object clause conjectures      : 29
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 27
% 0.14/0.38  # Proof object initial formulas used   : 19
% 0.14/0.38  # Proof object generating inferences   : 22
% 0.14/0.38  # Proof object simplifying inferences  : 55
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 19
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 36
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 35
% 0.14/0.38  # Processed clauses                    : 124
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 8
% 0.14/0.38  # ...remaining for further processing  : 116
% 0.14/0.38  # Other redundant clauses eliminated   : 3
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 30
% 0.14/0.38  # Generated clauses                    : 92
% 0.14/0.38  # ...of the previous two non-trivial   : 93
% 0.14/0.38  # Contextual simplify-reflections      : 2
% 0.14/0.38  # Paramodulations                      : 89
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 3
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 49
% 0.14/0.38  #    Positive orientable unit clauses  : 19
% 0.14/0.38  #    Positive unorientable unit clauses: 1
% 0.14/0.38  #    Negative unit clauses             : 4
% 0.14/0.38  #    Non-unit-clauses                  : 25
% 0.14/0.38  # Current number of unprocessed clauses: 38
% 0.14/0.38  # ...number of literals in the above   : 78
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 65
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 519
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 150
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.14/0.38  # Unit Clause-clause subsumption calls : 82
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 12
% 0.14/0.38  # BW rewrite match successes           : 6
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 4830
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.035 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.040 s
% 0.14/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
