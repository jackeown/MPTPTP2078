%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:18 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 694 expanded)
%              Number of clauses        :   67 ( 269 expanded)
%              Number of leaves         :   14 ( 172 expanded)
%              Depth                    :   15
%              Number of atoms          :  275 (2953 expanded)
%              Number of equality atoms :   40 ( 433 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & v1_tex_2(X2,X1) )
               => v1_tex_2(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_pre_topc(X3,X1)
               => ( ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    & v1_tex_2(X2,X1) )
                 => v1_tex_2(X3,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_tex_2])).

fof(c_0_15,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v1_tex_2(X26,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | X27 != u1_struct_0(X26)
        | v1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk1_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))
        | v1_tex_2(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( esk1_2(X25,X26) = u1_struct_0(X26)
        | v1_tex_2(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ v1_subset_1(esk1_2(X25,X26),u1_struct_0(X25))
        | v1_tex_2(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_16,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | r1_tarski(u1_struct_0(X24),u1_struct_0(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    & v1_tex_2(esk3_0,esk2_0)
    & ~ v1_tex_2(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_19,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | k2_struct_0(X11) = u1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_20,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | m1_subset_1(u1_struct_0(X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_23,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_tex_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( v1_tex_2(X1,X2)
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_30,plain,(
    ! [X29,X30] :
      ( ( ~ v1_subset_1(X30,X29)
        | X30 != X29
        | ~ m1_subset_1(X30,k1_zfmisc_1(X29)) )
      & ( X30 = X29
        | v1_subset_1(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_34,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

fof(c_0_35,plain,(
    ! [X19,X20] :
      ( ( ~ m1_pre_topc(X19,X20)
        | m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))
        | m1_pre_topc(X19,X20)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_36,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_37,plain,
    ( v1_tex_2(X1,X2)
    | ~ v1_subset_1(esk1_2(X2,X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_27]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_24]),c_0_25])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_25])])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_34])])).

fof(c_0_43,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_44,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( v1_tex_2(X1,X2)
    | ~ v1_subset_1(u1_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_49,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | m1_pre_topc(X18,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_50,plain,(
    ! [X8,X9,X10] :
      ( ( X10 != k1_pre_topc(X8,X9)
        | k2_struct_0(X10) = X9
        | ~ v1_pre_topc(X10)
        | ~ m1_pre_topc(X10,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( k2_struct_0(X10) != X9
        | X10 = k1_pre_topc(X8,X9)
        | ~ v1_pre_topc(X10)
        | ~ m1_pre_topc(X10,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_51,plain,(
    ! [X12,X13] :
      ( ( v1_pre_topc(k1_pre_topc(X12,X13))
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( m1_pre_topc(k1_pre_topc(X12,X13),X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_25])])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_46]),c_0_47]),c_0_24]),c_0_25])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_58,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk2_0) = k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_39]),c_0_57])])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_54]),c_0_55])])).

cnf(c_0_67,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk4_0,X1),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_61]),c_0_55])]),c_0_47]),c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_65]),c_0_25])])).

cnf(c_0_71,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_66]),c_0_55])])).

cnf(c_0_72,plain,
    ( k2_struct_0(k1_pre_topc(X1,u1_struct_0(X1))) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk4_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_69]),c_0_70])])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_55])).

cnf(c_0_76,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_65]),c_0_25])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_pre_topc(esk4_0,X1)),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_73]),c_0_70])])).

cnf(c_0_79,negated_conjecture,
    ( l1_struct_0(k1_pre_topc(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk4_0,u1_struct_0(esk2_0))) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_47]),c_0_47])).

cnf(c_0_81,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_76]),c_0_31])).

cnf(c_0_82,negated_conjecture,
    ( v1_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_27]),c_0_34])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k2_struct_0(k1_pre_topc(esk4_0,X1)),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_27]),c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk4_0,k2_struct_0(esk2_0))) = k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_27]),c_0_34])])).

cnf(c_0_87,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_88,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_65]),c_0_25])])).

cnf(c_0_89,negated_conjecture,
    ( u1_struct_0(esk3_0) = k2_struct_0(esk2_0)
    | ~ r1_tarski(k2_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_68])])).

cnf(c_0_91,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_27]),c_0_34])])).

cnf(c_0_93,negated_conjecture,
    ( u1_struct_0(esk3_0) = k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_94,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_68])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.21/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.028 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t14_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>((g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))&v1_tex_2(X2,X1))=>v1_tex_2(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tex_2)).
% 0.21/0.41  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.21/0.41  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.21/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.41  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.21/0.41  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.41  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.21/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.41  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.21/0.41  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.41  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.21/0.41  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.21/0.41  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.21/0.41  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>((g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))&v1_tex_2(X2,X1))=>v1_tex_2(X3,X1)))))), inference(assume_negation,[status(cth)],[t14_tex_2])).
% 0.21/0.41  fof(c_0_15, plain, ![X25, X26, X27]:((~v1_tex_2(X26,X25)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(X27!=u1_struct_0(X26)|v1_subset_1(X27,u1_struct_0(X25))))|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))&((m1_subset_1(esk1_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))|v1_tex_2(X26,X25)|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))&((esk1_2(X25,X26)=u1_struct_0(X26)|v1_tex_2(X26,X25)|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))&(~v1_subset_1(esk1_2(X25,X26),u1_struct_0(X25))|v1_tex_2(X26,X25)|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.21/0.41  fof(c_0_16, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|r1_tarski(u1_struct_0(X24),u1_struct_0(X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.21/0.41  fof(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_pre_topc(esk3_0,esk2_0)&(m1_pre_topc(esk4_0,esk2_0)&((g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))&v1_tex_2(esk3_0,esk2_0))&~v1_tex_2(esk4_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.41  fof(c_0_18, plain, ![X14]:(~l1_pre_topc(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.41  fof(c_0_19, plain, ![X11]:(~l1_struct_0(X11)|k2_struct_0(X11)=u1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.21/0.41  cnf(c_0_20, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  cnf(c_0_21, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  fof(c_0_22, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|m1_subset_1(u1_struct_0(X22),k1_zfmisc_1(u1_struct_0(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.41  cnf(c_0_23, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_26, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_27, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.41  cnf(c_0_28, negated_conjecture, (~v1_tex_2(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_29, plain, (v1_tex_2(X1,X2)|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.41  fof(c_0_30, plain, ![X29, X30]:((~v1_subset_1(X30,X29)|X30!=X29|~m1_subset_1(X30,k1_zfmisc_1(X29)))&(X30=X29|v1_subset_1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.21/0.41  cnf(c_0_31, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  fof(c_0_32, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.41  cnf(c_0_33, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_34, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.21/0.41  fof(c_0_35, plain, ![X19, X20]:((~m1_pre_topc(X19,X20)|m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))|~l1_pre_topc(X20)|~l1_pre_topc(X19))&(~m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))|m1_pre_topc(X19,X20)|~l1_pre_topc(X20)|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.21/0.41  fof(c_0_36, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|l1_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.41  cnf(c_0_37, plain, (v1_tex_2(X1,X2)|~v1_subset_1(esk1_2(X2,X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_27]), c_0_26])).
% 0.21/0.41  cnf(c_0_38, negated_conjecture, (~v1_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_39, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  cnf(c_0_40, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.41  cnf(c_0_42, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),k2_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_27]), c_0_34])])).
% 0.21/0.41  fof(c_0_43, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.41  cnf(c_0_44, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.41  cnf(c_0_45, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.41  cnf(c_0_46, plain, (v1_tex_2(X1,X2)|~v1_subset_1(u1_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_37, c_0_21])).
% 0.21/0.41  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.21/0.41  cnf(c_0_48, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.41  fof(c_0_49, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|m1_pre_topc(X18,X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.21/0.41  fof(c_0_50, plain, ![X8, X9, X10]:((X10!=k1_pre_topc(X8,X9)|k2_struct_0(X10)=X9|(~v1_pre_topc(X10)|~m1_pre_topc(X10,X8))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(k2_struct_0(X10)!=X9|X10=k1_pre_topc(X8,X9)|(~v1_pre_topc(X10)|~m1_pre_topc(X10,X8))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.21/0.41  fof(c_0_51, plain, ![X12, X13]:((v1_pre_topc(k1_pre_topc(X12,X13))|(~l1_pre_topc(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))&(m1_pre_topc(k1_pre_topc(X12,X13),X12)|(~l1_pre_topc(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.21/0.41  cnf(c_0_52, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.41  cnf(c_0_53, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.41  cnf(c_0_54, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_56, negated_conjecture, (~v1_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_46]), c_0_47]), c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_48, c_0_47])).
% 0.21/0.41  cnf(c_0_58, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.41  cnf(c_0_59, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.41  cnf(c_0_60, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.41  cnf(c_0_61, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.41  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_52])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.21/0.41  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk2_0)=k2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_39]), c_0_57])])).
% 0.21/0.41  cnf(c_0_65, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_66, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_54]), c_0_55])])).
% 0.21/0.41  cnf(c_0_67, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_59]), c_0_60]), c_0_61])).
% 0.21/0.41  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_62])).
% 0.21/0.41  cnf(c_0_69, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk4_0,X1),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_61]), c_0_55])]), c_0_47]), c_0_64])).
% 0.21/0.41  cnf(c_0_70, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_65]), c_0_25])])).
% 0.21/0.41  cnf(c_0_71, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_66]), c_0_55])])).
% 0.21/0.41  cnf(c_0_72, plain, (k2_struct_0(k1_pre_topc(X1,u1_struct_0(X1)))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.41  cnf(c_0_73, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk4_0,X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_69]), c_0_70])])).
% 0.21/0.41  cnf(c_0_74, negated_conjecture, (l1_pre_topc(k1_pre_topc(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_71, c_0_69])).
% 0.21/0.41  cnf(c_0_75, negated_conjecture, (k2_struct_0(k1_pre_topc(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_72, c_0_55])).
% 0.21/0.41  cnf(c_0_76, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  cnf(c_0_77, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_65]), c_0_25])])).
% 0.21/0.41  cnf(c_0_78, negated_conjecture, (r1_tarski(u1_struct_0(k1_pre_topc(esk4_0,X1)),u1_struct_0(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_73]), c_0_70])])).
% 0.21/0.41  cnf(c_0_79, negated_conjecture, (l1_struct_0(k1_pre_topc(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_26, c_0_74])).
% 0.21/0.41  cnf(c_0_80, negated_conjecture, (k2_struct_0(k1_pre_topc(esk4_0,u1_struct_0(esk2_0)))=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_47]), c_0_47])).
% 0.21/0.41  cnf(c_0_81, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_76]), c_0_31])).
% 0.21/0.41  cnf(c_0_82, negated_conjecture, (v1_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_83, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.41  cnf(c_0_84, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),k2_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_27]), c_0_34])])).
% 0.21/0.41  cnf(c_0_85, negated_conjecture, (r1_tarski(k2_struct_0(k1_pre_topc(esk4_0,X1)),u1_struct_0(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_27]), c_0_79])).
% 0.21/0.41  cnf(c_0_86, negated_conjecture, (k2_struct_0(k1_pre_topc(esk4_0,k2_struct_0(esk2_0)))=k2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_27]), c_0_34])])).
% 0.21/0.41  cnf(c_0_87, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  cnf(c_0_88, negated_conjecture, (v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_65]), c_0_25])])).
% 0.21/0.41  cnf(c_0_89, negated_conjecture, (u1_struct_0(esk3_0)=k2_struct_0(esk2_0)|~r1_tarski(k2_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.21/0.41  cnf(c_0_90, negated_conjecture, (r1_tarski(k2_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_68])])).
% 0.21/0.41  cnf(c_0_91, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_87])).
% 0.21/0.41  cnf(c_0_92, negated_conjecture, (v1_subset_1(u1_struct_0(esk3_0),k2_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_27]), c_0_34])])).
% 0.21/0.41  cnf(c_0_93, negated_conjecture, (u1_struct_0(esk3_0)=k2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])])).
% 0.21/0.41  cnf(c_0_94, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_68])])).
% 0.21/0.41  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93]), c_0_94]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 96
% 0.21/0.41  # Proof object clause steps            : 67
% 0.21/0.41  # Proof object formula steps           : 29
% 0.21/0.41  # Proof object conjectures             : 41
% 0.21/0.41  # Proof object clause conjectures      : 38
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 24
% 0.21/0.41  # Proof object initial formulas used   : 14
% 0.21/0.41  # Proof object generating inferences   : 33
% 0.21/0.41  # Proof object simplifying inferences  : 67
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 14
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 29
% 0.21/0.41  # Removed in clause preprocessing      : 0
% 0.21/0.41  # Initial clauses in saturation        : 29
% 0.21/0.41  # Processed clauses                    : 417
% 0.21/0.41  # ...of these trivial                  : 17
% 0.21/0.41  # ...subsumed                          : 110
% 0.21/0.41  # ...remaining for further processing  : 290
% 0.21/0.41  # Other redundant clauses eliminated   : 6
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 0
% 0.21/0.41  # Backward-rewritten                   : 102
% 0.21/0.41  # Generated clauses                    : 898
% 0.21/0.41  # ...of the previous two non-trivial   : 902
% 0.21/0.41  # Contextual simplify-reflections      : 15
% 0.21/0.41  # Paramodulations                      : 892
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 6
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 155
% 0.21/0.41  #    Positive orientable unit clauses  : 29
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 2
% 0.21/0.41  #    Non-unit-clauses                  : 124
% 0.21/0.41  # Current number of unprocessed clauses: 455
% 0.21/0.41  # ...number of literals in the above   : 1875
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 129
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 3246
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 2248
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 117
% 0.21/0.41  # Unit Clause-clause subsumption calls : 99
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 24
% 0.21/0.41  # BW rewrite match successes           : 6
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 23618
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.059 s
% 0.21/0.41  # System time              : 0.006 s
% 0.21/0.41  # Total time               : 0.064 s
% 0.21/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
