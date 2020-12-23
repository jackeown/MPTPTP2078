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
% DateTime   : Thu Dec  3 11:20:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 (4184 expanded)
%              Number of clauses        :   63 (1546 expanded)
%              Number of leaves         :   13 (1026 expanded)
%              Depth                    :   17
%              Number of atoms          :  354 (22673 expanded)
%              Number of equality atoms :   35 ( 964 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   31 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(t43_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(rc3_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2)
          & ~ v1_zfmisc_1(X2)
          & ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tex_2)).

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

fof(cc2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_xboole_0(X2)
           => ~ v1_subset_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t46_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t8_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X42,X43] :
      ( v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ v1_tdlat_3(X42)
      | ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | v2_tex_2(X43,X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & v1_tdlat_3(esk6_0)
    & l1_pre_topc(esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & ( ~ v3_tex_2(esk7_0,esk6_0)
      | v1_subset_1(esk7_0,u1_struct_0(esk6_0)) )
    & ( v3_tex_2(esk7_0,esk6_0)
      | ~ v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X34,X35] :
      ( ( ~ v1_subset_1(X35,X34)
        | X35 != X34
        | ~ m1_subset_1(X35,k1_zfmisc_1(X34)) )
      & ( X35 = X34
        | v1_subset_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_tdlat_3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X40] :
      ( ( m1_subset_1(esk5_1(X40),k1_zfmisc_1(X40))
        | v1_xboole_0(X40)
        | v1_zfmisc_1(X40) )
      & ( ~ v1_xboole_0(esk5_1(X40))
        | v1_xboole_0(X40)
        | v1_zfmisc_1(X40) )
      & ( ~ v1_zfmisc_1(esk5_1(X40))
        | v1_xboole_0(X40)
        | v1_zfmisc_1(X40) )
      & ( ~ v1_subset_1(esk5_1(X40),X40)
        | v1_xboole_0(X40)
        | v1_zfmisc_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_tex_2])])])])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X36,X37,X38] :
      ( ( v2_tex_2(X37,X36)
        | ~ v3_tex_2(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) )
      & ( ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_tex_2(X38,X36)
        | ~ r1_tarski(X37,X38)
        | X37 = X38
        | ~ v3_tex_2(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) )
      & ( m1_subset_1(esk4_2(X36,X37),k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_tex_2(X37,X36)
        | v3_tex_2(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) )
      & ( v2_tex_2(esk4_2(X36,X37),X36)
        | ~ v2_tex_2(X37,X36)
        | v3_tex_2(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) )
      & ( r1_tarski(X37,esk4_2(X36,X37))
        | ~ v2_tex_2(X37,X36)
        | v3_tex_2(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) )
      & ( X37 != esk4_2(X36,X37)
        | ~ v2_tex_2(X37,X36)
        | v3_tex_2(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

cnf(c_0_26,negated_conjecture,
    ( v2_tex_2(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X32,X33] :
      ( v1_xboole_0(X32)
      | ~ v1_zfmisc_1(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | v1_xboole_0(X33)
      | ~ v1_subset_1(X33,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_29,plain,(
    ! [X20,X21] :
      ( ~ v1_xboole_0(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | v1_xboole_0(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_30,plain,(
    ! [X44,X45] :
      ( v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | ~ v1_xboole_0(X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
      | ~ v3_tex_2(X45,X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).

cnf(c_0_31,negated_conjecture,
    ( v3_tex_2(esk7_0,esk6_0)
    | ~ v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v2_tex_2(esk5_1(u1_struct_0(esk6_0)),esk6_0)
    | v1_zfmisc_1(u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | ~ v1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | v3_tex_2(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( esk5_1(u1_struct_0(esk6_0)) = X1
    | v1_zfmisc_1(u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ v3_tex_2(X1,esk6_0)
    | ~ r1_tarski(X1,esk5_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_20])]),c_0_27])).

cnf(c_0_42,plain,
    ( esk5_1(X1) = X1
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_35])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X1,X2)
    | ~ v1_zfmisc_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_19]),c_0_20]),c_0_24])]),c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk6_0) = X1
    | v1_zfmisc_1(u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ v3_tex_2(X1,esk6_0)
    | ~ r1_tarski(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_24])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ v1_zfmisc_1(u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_32]),c_0_24])]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_40]),c_0_49])).

fof(c_0_52,plain,(
    ! [X16,X17,X18] :
      ( ( m1_subset_1(esk2_3(X16,X17,X18),X16)
        | X17 = X18
        | ~ m1_subset_1(X18,k1_zfmisc_1(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X17 = X18
        | ~ m1_subset_1(X18,k1_zfmisc_1(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X17 = X18
        | ~ m1_subset_1(X18,k1_zfmisc_1(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

cnf(c_0_53,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_46])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_57,negated_conjecture,
    ( v2_tex_2(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_58,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_54])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,esk4_2(X2,X1))
    | v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_61,negated_conjecture,
    ( X1 = esk7_0
    | m1_subset_1(esk2_3(u1_struct_0(esk6_0),X1,esk7_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( v3_tex_2(esk7_0,esk6_0)
    | m1_subset_1(esk4_2(esk6_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_20]),c_0_24])])).

cnf(c_0_63,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
    | ~ v3_tex_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_subset_1(esk7_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( v3_tex_2(esk7_0,esk6_0)
    | r1_tarski(esk7_0,esk4_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_57]),c_0_20]),c_0_24])])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_67,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ r2_hidden(X10,X9)
      | r2_hidden(X10,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_68,plain,(
    ! [X5,X6] :
      ( ( ~ m1_subset_1(X6,X5)
        | r2_hidden(X6,X5)
        | v1_xboole_0(X5) )
      & ( ~ r2_hidden(X6,X5)
        | m1_subset_1(X6,X5)
        | v1_xboole_0(X5) )
      & ( ~ m1_subset_1(X6,X5)
        | v1_xboole_0(X6)
        | ~ v1_xboole_0(X5) )
      & ( ~ v1_xboole_0(X6)
        | m1_subset_1(X6,X5)
        | ~ v1_xboole_0(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_69,negated_conjecture,
    ( esk4_2(esk6_0,esk7_0) = esk7_0
    | v3_tex_2(esk7_0,esk6_0)
    | m1_subset_1(esk2_3(u1_struct_0(esk6_0),esk4_2(esk6_0,esk7_0),esk7_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( ~ v3_tex_2(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_54]),c_0_64])).

fof(c_0_71,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | ~ v1_xboole_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_72,negated_conjecture,
    ( v3_tex_2(esk7_0,esk6_0)
    | m1_subset_1(esk7_0,k1_zfmisc_1(esk4_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(esk2_3(u1_struct_0(esk6_0),X1,esk7_0),esk7_0)
    | r2_hidden(esk2_3(u1_struct_0(esk6_0),X1,esk7_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_24])).

cnf(c_0_74,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( esk4_2(esk6_0,esk7_0) = esk7_0
    | m1_subset_1(esk2_3(esk7_0,esk4_2(esk6_0,esk7_0),esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_54]),c_0_54]),c_0_70])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk4_2(esk6_0,esk7_0),k1_zfmisc_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_54]),c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_2(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[c_0_72,c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(esk2_3(esk7_0,X1,esk7_0),esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_54]),c_0_54]),c_0_54]),c_0_74])).

cnf(c_0_81,plain,
    ( X2 = X3
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_82,negated_conjecture,
    ( esk4_2(esk6_0,esk7_0) = esk7_0
    | r2_hidden(esk2_3(esk7_0,esk4_2(esk6_0,esk7_0),esk7_0),esk7_0)
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_2(esk6_0,esk7_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,esk4_2(esk6_0,esk7_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( esk4_2(esk6_0,esk7_0) = esk7_0
    | r2_hidden(esk2_3(esk7_0,esk4_2(esk6_0,esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( esk4_2(esk6_0,esk7_0) = esk7_0
    | ~ r2_hidden(esk2_3(esk7_0,esk4_2(esk6_0,esk7_0),esk7_0),esk4_2(esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_59]),c_0_78])]),c_0_83])).

cnf(c_0_87,plain,
    ( v3_tex_2(X1,X2)
    | X1 != esk4_2(X2,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_88,negated_conjecture,
    ( esk4_2(esk6_0,esk7_0) = esk7_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_57]),c_0_20]),c_0_54]),c_0_59])]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:05:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.19/0.52  # and selection function PSelectComplexPreferEQ.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.045 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t49_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 0.19/0.52  fof(t43_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 0.19/0.52  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.52  fof(rc3_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>?[X2]:(((m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_xboole_0(X2)))&~(v1_zfmisc_1(X2)))&~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tex_2)).
% 0.19/0.52  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 0.19/0.52  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.19/0.52  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.52  fof(t46_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 0.19/0.52  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.52  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 0.19/0.52  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.52  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.52  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.52  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>~(v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t49_tex_2])).
% 0.19/0.52  fof(c_0_14, plain, ![X42, X43]:(v2_struct_0(X42)|~v2_pre_topc(X42)|~v1_tdlat_3(X42)|~l1_pre_topc(X42)|(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|v2_tex_2(X43,X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tex_2])])])])).
% 0.19/0.52  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&v1_tdlat_3(esk6_0))&l1_pre_topc(esk6_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))&((~v3_tex_2(esk7_0,esk6_0)|v1_subset_1(esk7_0,u1_struct_0(esk6_0)))&(v3_tex_2(esk7_0,esk6_0)|~v1_subset_1(esk7_0,u1_struct_0(esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.19/0.52  fof(c_0_16, plain, ![X34, X35]:((~v1_subset_1(X35,X34)|X35!=X34|~m1_subset_1(X35,k1_zfmisc_1(X34)))&(X35=X34|v1_subset_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.52  cnf(c_0_17, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.52  cnf(c_0_18, negated_conjecture, (v1_tdlat_3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  fof(c_0_22, plain, ![X40]:((((m1_subset_1(esk5_1(X40),k1_zfmisc_1(X40))|(v1_xboole_0(X40)|v1_zfmisc_1(X40)))&(~v1_xboole_0(esk5_1(X40))|(v1_xboole_0(X40)|v1_zfmisc_1(X40))))&(~v1_zfmisc_1(esk5_1(X40))|(v1_xboole_0(X40)|v1_zfmisc_1(X40))))&(~v1_subset_1(esk5_1(X40),X40)|(v1_xboole_0(X40)|v1_zfmisc_1(X40)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_tex_2])])])])])).
% 0.19/0.52  cnf(c_0_23, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  fof(c_0_25, plain, ![X36, X37, X38]:(((v2_tex_2(X37,X36)|~v3_tex_2(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36))&(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|(~v2_tex_2(X38,X36)|~r1_tarski(X37,X38)|X37=X38)|~v3_tex_2(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36)))&((m1_subset_1(esk4_2(X36,X37),k1_zfmisc_1(u1_struct_0(X36)))|~v2_tex_2(X37,X36)|v3_tex_2(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36))&(((v2_tex_2(esk4_2(X36,X37),X36)|~v2_tex_2(X37,X36)|v3_tex_2(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36))&(r1_tarski(X37,esk4_2(X36,X37))|~v2_tex_2(X37,X36)|v3_tex_2(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36)))&(X37!=esk4_2(X36,X37)|~v2_tex_2(X37,X36)|v3_tex_2(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X36))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.19/0.52  cnf(c_0_26, negated_conjecture, (v2_tex_2(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.52  cnf(c_0_27, plain, (m1_subset_1(esk5_1(X1),k1_zfmisc_1(X1))|v1_xboole_0(X1)|v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.52  fof(c_0_28, plain, ![X32, X33]:(v1_xboole_0(X32)|~v1_zfmisc_1(X32)|(~m1_subset_1(X33,k1_zfmisc_1(X32))|(v1_xboole_0(X33)|~v1_subset_1(X33,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.19/0.52  fof(c_0_29, plain, ![X20, X21]:(~v1_xboole_0(X20)|(~m1_subset_1(X21,k1_zfmisc_1(X20))|v1_xboole_0(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.52  fof(c_0_30, plain, ![X44, X45]:(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(~v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~v3_tex_2(X45,X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).
% 0.19/0.52  cnf(c_0_31, negated_conjecture, (v3_tex_2(esk7_0,esk6_0)|~v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_32, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.52  cnf(c_0_33, plain, (X3=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X1,X2)|~r1_tarski(X3,X1)|~v3_tex_2(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_34, negated_conjecture, (v2_tex_2(esk5_1(u1_struct_0(esk6_0)),esk6_0)|v1_zfmisc_1(u1_struct_0(esk6_0))|v1_xboole_0(u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.52  cnf(c_0_35, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|~v1_subset_1(esk5_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.52  fof(c_0_36, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.52  cnf(c_0_37, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.52  cnf(c_0_38, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_39, plain, (v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.52  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|v3_tex_2(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.52  cnf(c_0_41, negated_conjecture, (esk5_1(u1_struct_0(esk6_0))=X1|v1_zfmisc_1(u1_struct_0(esk6_0))|v1_xboole_0(u1_struct_0(esk6_0))|~v3_tex_2(X1,esk6_0)|~r1_tarski(X1,esk5_1(u1_struct_0(esk6_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_20])]), c_0_27])).
% 0.19/0.52  cnf(c_0_42, plain, (esk5_1(X1)=X1|v1_zfmisc_1(X1)|v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_35])).
% 0.19/0.52  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.52  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.52  cnf(c_0_45, plain, (v1_xboole_0(X1)|~v1_subset_1(X1,X2)|~v1_zfmisc_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.52  cnf(c_0_46, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~v1_xboole_0(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_19]), c_0_20]), c_0_24])]), c_0_21])).
% 0.19/0.52  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk6_0)=X1|v1_zfmisc_1(u1_struct_0(esk6_0))|v1_xboole_0(u1_struct_0(esk6_0))|~v3_tex_2(X1,esk6_0)|~r1_tarski(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.19/0.52  cnf(c_0_48, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_44, c_0_24])).
% 0.19/0.52  cnf(c_0_49, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~v1_zfmisc_1(u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_32]), c_0_24])]), c_0_46])).
% 0.19/0.52  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_24])).
% 0.19/0.52  cnf(c_0_51, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|v1_xboole_0(u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_40]), c_0_49])).
% 0.19/0.52  fof(c_0_52, plain, ![X16, X17, X18]:((m1_subset_1(esk2_3(X16,X17,X18),X16)|X17=X18|~m1_subset_1(X18,k1_zfmisc_1(X16))|~m1_subset_1(X17,k1_zfmisc_1(X16)))&((~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X17=X18|~m1_subset_1(X18,k1_zfmisc_1(X16))|~m1_subset_1(X17,k1_zfmisc_1(X16)))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X17=X18|~m1_subset_1(X18,k1_zfmisc_1(X16))|~m1_subset_1(X17,k1_zfmisc_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.19/0.52  cnf(c_0_53, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  cnf(c_0_54, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_46])).
% 0.19/0.52  cnf(c_0_55, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.52  cnf(c_0_56, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_57, negated_conjecture, (v2_tex_2(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.19/0.52  cnf(c_0_58, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_53])).
% 0.19/0.52  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk7_0))), inference(rw,[status(thm)],[c_0_24, c_0_54])).
% 0.19/0.52  cnf(c_0_60, plain, (r1_tarski(X1,esk4_2(X2,X1))|v3_tex_2(X1,X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_61, negated_conjecture, (X1=esk7_0|m1_subset_1(esk2_3(u1_struct_0(esk6_0),X1,esk7_0),u1_struct_0(esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_55, c_0_24])).
% 0.19/0.52  cnf(c_0_62, negated_conjecture, (v3_tex_2(esk7_0,esk6_0)|m1_subset_1(esk4_2(esk6_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_20]), c_0_24])])).
% 0.19/0.52  cnf(c_0_63, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~v3_tex_2(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_64, negated_conjecture, (~v1_subset_1(esk7_0,esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.52  cnf(c_0_65, negated_conjecture, (v3_tex_2(esk7_0,esk6_0)|r1_tarski(esk7_0,esk4_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_57]), c_0_20]), c_0_24])])).
% 0.19/0.52  cnf(c_0_66, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.52  fof(c_0_67, plain, ![X8, X9, X10]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|(~r2_hidden(X10,X9)|r2_hidden(X10,X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.52  fof(c_0_68, plain, ![X5, X6]:(((~m1_subset_1(X6,X5)|r2_hidden(X6,X5)|v1_xboole_0(X5))&(~r2_hidden(X6,X5)|m1_subset_1(X6,X5)|v1_xboole_0(X5)))&((~m1_subset_1(X6,X5)|v1_xboole_0(X6)|~v1_xboole_0(X5))&(~v1_xboole_0(X6)|m1_subset_1(X6,X5)|~v1_xboole_0(X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.52  cnf(c_0_69, negated_conjecture, (esk4_2(esk6_0,esk7_0)=esk7_0|v3_tex_2(esk7_0,esk6_0)|m1_subset_1(esk2_3(u1_struct_0(esk6_0),esk4_2(esk6_0,esk7_0),esk7_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.52  cnf(c_0_70, negated_conjecture, (~v3_tex_2(esk7_0,esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_54]), c_0_64])).
% 0.19/0.52  fof(c_0_71, plain, ![X27, X28, X29]:(~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X29))|~v1_xboole_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.52  cnf(c_0_72, negated_conjecture, (v3_tex_2(esk7_0,esk6_0)|m1_subset_1(esk7_0,k1_zfmisc_1(esk4_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_43, c_0_65])).
% 0.19/0.52  cnf(c_0_73, negated_conjecture, (X1=esk7_0|r2_hidden(esk2_3(u1_struct_0(esk6_0),X1,esk7_0),esk7_0)|r2_hidden(esk2_3(u1_struct_0(esk6_0),X1,esk7_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_66, c_0_24])).
% 0.19/0.52  cnf(c_0_74, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.52  cnf(c_0_75, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.52  cnf(c_0_76, negated_conjecture, (esk4_2(esk6_0,esk7_0)=esk7_0|m1_subset_1(esk2_3(esk7_0,esk4_2(esk6_0,esk7_0),esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_54]), c_0_54]), c_0_70])).
% 0.19/0.52  cnf(c_0_77, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.52  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk4_2(esk6_0,esk7_0),k1_zfmisc_1(esk7_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_54]), c_0_70])).
% 0.19/0.52  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_2(esk6_0,esk7_0)))), inference(sr,[status(thm)],[c_0_72, c_0_70])).
% 0.19/0.52  cnf(c_0_80, negated_conjecture, (X1=esk7_0|r2_hidden(esk2_3(esk7_0,X1,esk7_0),esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(esk7_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_54]), c_0_54]), c_0_54]), c_0_74])).
% 0.19/0.52  cnf(c_0_81, plain, (X2=X3|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.52  cnf(c_0_82, negated_conjecture, (esk4_2(esk6_0,esk7_0)=esk7_0|r2_hidden(esk2_3(esk7_0,esk4_2(esk6_0,esk7_0),esk7_0),esk7_0)|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.52  cnf(c_0_83, negated_conjecture, (~r2_hidden(X1,esk4_2(esk6_0,esk7_0))|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.52  cnf(c_0_84, negated_conjecture, (r2_hidden(X1,esk4_2(esk6_0,esk7_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_74, c_0_79])).
% 0.19/0.52  cnf(c_0_85, negated_conjecture, (esk4_2(esk6_0,esk7_0)=esk7_0|r2_hidden(esk2_3(esk7_0,esk4_2(esk6_0,esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_80, c_0_78])).
% 0.19/0.52  cnf(c_0_86, negated_conjecture, (esk4_2(esk6_0,esk7_0)=esk7_0|~r2_hidden(esk2_3(esk7_0,esk4_2(esk6_0,esk7_0),esk7_0),esk4_2(esk6_0,esk7_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_59]), c_0_78])]), c_0_83])).
% 0.19/0.52  cnf(c_0_87, plain, (v3_tex_2(X1,X2)|X1!=esk4_2(X2,X1)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_88, negated_conjecture, (esk4_2(esk6_0,esk7_0)=esk7_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 0.19/0.52  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_57]), c_0_20]), c_0_54]), c_0_59])]), c_0_70]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 90
% 0.19/0.52  # Proof object clause steps            : 63
% 0.19/0.52  # Proof object formula steps           : 27
% 0.19/0.52  # Proof object conjectures             : 43
% 0.19/0.52  # Proof object clause conjectures      : 40
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 27
% 0.19/0.52  # Proof object initial formulas used   : 13
% 0.19/0.52  # Proof object generating inferences   : 28
% 0.19/0.52  # Proof object simplifying inferences  : 52
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 20
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 43
% 0.19/0.52  # Removed in clause preprocessing      : 0
% 0.19/0.52  # Initial clauses in saturation        : 43
% 0.19/0.52  # Processed clauses                    : 1156
% 0.19/0.52  # ...of these trivial                  : 33
% 0.19/0.52  # ...subsumed                          : 455
% 0.19/0.52  # ...remaining for further processing  : 668
% 0.19/0.52  # Other redundant clauses eliminated   : 1
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 62
% 0.19/0.52  # Backward-rewritten                   : 308
% 0.19/0.52  # Generated clauses                    : 2946
% 0.19/0.52  # ...of the previous two non-trivial   : 3018
% 0.19/0.52  # Contextual simplify-reflections      : 47
% 0.19/0.52  # Paramodulations                      : 2896
% 0.19/0.52  # Factorizations                       : 34
% 0.19/0.52  # Equation resolutions                 : 1
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 239
% 0.19/0.52  #    Positive orientable unit clauses  : 18
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 5
% 0.19/0.52  #    Non-unit-clauses                  : 216
% 0.19/0.52  # Current number of unprocessed clauses: 1686
% 0.19/0.52  # ...number of literals in the above   : 8554
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 428
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 21651
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 6180
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 470
% 0.19/0.52  # Unit Clause-clause subsumption calls : 389
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 9
% 0.19/0.52  # BW rewrite match successes           : 9
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 75457
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.175 s
% 0.19/0.52  # System time              : 0.006 s
% 0.19/0.52  # Total time               : 0.181 s
% 0.19/0.52  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
