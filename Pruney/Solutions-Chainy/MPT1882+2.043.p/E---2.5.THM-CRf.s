%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 189 expanded)
%              Number of clauses        :   33 (  64 expanded)
%              Number of leaves         :    6 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  240 (1394 expanded)
%              Number of equality atoms :    7 (  25 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   31 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v3_tex_2(X2,X1)
          <=> v1_zfmisc_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(t44_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_tex_2(X2,X1)
          <=> v1_zfmisc_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v2_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v3_tex_2(X2,X1)
            <=> v1_zfmisc_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tex_2])).

fof(c_0_7,plain,(
    ! [X20,X21] :
      ( ( ~ v2_tex_2(X21,X20)
        | v1_zfmisc_1(X21)
        | v1_xboole_0(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ v2_tdlat_3(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ v1_zfmisc_1(X21)
        | v2_tex_2(X21,X20)
        | v1_xboole_0(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ v2_tdlat_3(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_tex_2])])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & v2_tdlat_3(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v3_tex_2(esk5_0,esk4_0)
      | ~ v1_zfmisc_1(esk5_0) )
    & ( v3_tex_2(esk5_0,esk4_0)
      | v1_zfmisc_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] :
      ( ( v2_tex_2(X15,X14)
        | ~ v3_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v2_tex_2(X16,X14)
        | ~ r1_tarski(X15,X16)
        | X15 = X16
        | ~ v3_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v2_tex_2(X15,X14)
        | v3_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( v2_tex_2(esk3_2(X14,X15),X14)
        | ~ v2_tex_2(X15,X14)
        | v3_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( r1_tarski(X15,esk3_2(X14,X15))
        | ~ v2_tex_2(X15,X14)
        | v3_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( X15 != esk3_2(X14,X15)
        | ~ v2_tex_2(X15,X14)
        | v3_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( v1_xboole_0(X18)
      | v1_xboole_0(X19)
      | ~ v1_zfmisc_1(X19)
      | ~ r1_tarski(X18,X19)
      | X18 = X19 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_12,plain,
    ( v2_tex_2(X1,X2)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v2_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_19,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,esk3_2(X2,X1))
    | v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v3_tex_2(X1,X2)
    | X1 != esk3_2(X2,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( v2_tex_2(esk3_2(X1,X2),X1)
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0)
    | ~ v1_zfmisc_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v3_tex_2(esk5_0,esk4_0)
    | v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( v3_tex_2(X1,X2)
    | r2_hidden(X3,esk3_2(X2,X1))
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( v3_tex_2(X1,X2)
    | v1_xboole_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(esk3_2(X2,X1))
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_23])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(esk3_2(X1,X2))
    | v3_tex_2(X2,X1)
    | v1_xboole_0(esk3_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0)
    | v3_tex_2(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(esk3_2(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | v1_xboole_0(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v1_zfmisc_1(esk5_0)
    | ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_13]),c_0_16])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( ~ v3_tex_2(esk5_0,esk4_0)
    | ~ v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( v1_zfmisc_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | v1_xboole_0(X2)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( ~ v3_tex_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_13]),c_0_14]),c_0_15]),c_0_38]),c_0_16])]),c_0_17]),c_0_44]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t50_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v3_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 0.19/0.37  fof(t44_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 0.19/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.37  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 0.19/0.37  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 0.19/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v3_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t50_tex_2])).
% 0.19/0.37  fof(c_0_7, plain, ![X20, X21]:((~v2_tex_2(X21,X20)|v1_zfmisc_1(X21)|(v1_xboole_0(X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~v2_tdlat_3(X20)|~l1_pre_topc(X20)))&(~v1_zfmisc_1(X21)|v2_tex_2(X21,X20)|(v1_xboole_0(X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~v2_tdlat_3(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_tex_2])])])])])).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v2_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v3_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0))&(v3_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.19/0.37  fof(c_0_9, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.37  fof(c_0_10, plain, ![X14, X15, X16]:(((v2_tex_2(X15,X14)|~v3_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(~v2_tex_2(X16,X14)|~r1_tarski(X15,X16)|X15=X16)|~v3_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14)))&((m1_subset_1(esk3_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|~v2_tex_2(X15,X14)|v3_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(((v2_tex_2(esk3_2(X14,X15),X14)|~v2_tex_2(X15,X14)|v3_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(r1_tarski(X15,esk3_2(X14,X15))|~v2_tex_2(X15,X14)|v3_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14)))&(X15!=esk3_2(X14,X15)|~v2_tex_2(X15,X14)|v3_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X18, X19]:(v1_xboole_0(X18)|(v1_xboole_0(X19)|~v1_zfmisc_1(X19)|(~r1_tarski(X18,X19)|X18=X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.19/0.37  cnf(c_0_12, plain, (v2_tex_2(X1,X2)|v1_xboole_0(X1)|v2_struct_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~v2_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (v2_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  fof(c_0_19, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.37  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_21, plain, (r1_tarski(X1,esk3_2(X2,X1))|v3_tex_2(X1,X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_22, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_23, plain, (v3_tex_2(X1,X2)|X1!=esk3_2(X2,X1)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_24, plain, (v1_zfmisc_1(X1)|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~v2_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_25, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_26, plain, (v2_tex_2(esk3_2(X1,X2),X1)|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17]), c_0_18])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (v3_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_30, plain, (v3_tex_2(X1,X2)|r2_hidden(X3,esk3_2(X2,X1))|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  cnf(c_0_31, plain, (v3_tex_2(X1,X2)|v1_xboole_0(esk3_2(X2,X1))|v1_xboole_0(X1)|~v1_zfmisc_1(esk3_2(X2,X1))|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_21]), c_0_23])).
% 0.19/0.37  cnf(c_0_32, plain, (v2_struct_0(X1)|v1_zfmisc_1(esk3_2(X1,X2))|v3_tex_2(X2,X1)|v1_xboole_0(esk3_2(X1,X2))|~v2_tdlat_3(X1)|~v2_pre_topc(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.19/0.37  cnf(c_0_33, plain, (v2_tex_2(X1,X2)|~v3_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)|v3_tex_2(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.37  cnf(c_0_35, plain, (v3_tex_2(X1,X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X3,X1)|~v1_xboole_0(esk3_2(X2,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  cnf(c_0_36, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|v1_xboole_0(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tdlat_3(X1)|~v2_pre_topc(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (v1_zfmisc_1(esk5_0)|~v2_tex_2(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17]), c_0_18])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_13]), c_0_16])])).
% 0.19/0.37  cnf(c_0_39, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|~v2_tdlat_3(X1)|~v2_pre_topc(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_29])).
% 0.19/0.37  cnf(c_0_40, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (~v3_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (v1_zfmisc_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.19/0.37  cnf(c_0_43, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|v1_xboole_0(X2)|~v2_tdlat_3(X1)|~v2_pre_topc(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (~v3_tex_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_13]), c_0_14]), c_0_15]), c_0_38]), c_0_16])]), c_0_17]), c_0_44]), c_0_18]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 46
% 0.19/0.37  # Proof object clause steps            : 33
% 0.19/0.37  # Proof object formula steps           : 13
% 0.19/0.37  # Proof object conjectures             : 18
% 0.19/0.37  # Proof object clause conjectures      : 15
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 19
% 0.19/0.37  # Proof object initial formulas used   : 6
% 0.19/0.37  # Proof object generating inferences   : 12
% 0.19/0.37  # Proof object simplifying inferences  : 30
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 6
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 22
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 22
% 0.19/0.37  # Processed clauses                    : 64
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 2
% 0.19/0.37  # ...remaining for further processing  : 62
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 2
% 0.19/0.37  # Backward-rewritten                   : 4
% 0.19/0.37  # Generated clauses                    : 30
% 0.19/0.37  # ...of the previous two non-trivial   : 25
% 0.19/0.37  # Contextual simplify-reflections      : 4
% 0.19/0.37  # Paramodulations                      : 30
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 34
% 0.19/0.37  #    Positive orientable unit clauses  : 7
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 24
% 0.19/0.37  # Current number of unprocessed clauses: 4
% 0.19/0.37  # ...number of literals in the above   : 39
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 28
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 312
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 39
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.19/0.37  # Unit Clause-clause subsumption calls : 16
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 6
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2847
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.033 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
