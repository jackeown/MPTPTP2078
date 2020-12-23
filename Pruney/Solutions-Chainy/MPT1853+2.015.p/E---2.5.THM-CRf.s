%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 283 expanded)
%              Number of clauses        :   49 ( 107 expanded)
%              Number of leaves         :   19 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  317 (1244 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_tex_2(k1_tex_2(X1,X2),X1)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(cc10_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ~ v2_struct_0(X2)
           => ( ~ v2_struct_0(X2)
              & ~ v1_tex_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

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

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc6_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t7_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(cc5_funct_1,axiom,(
    ! [X1] :
      ( v1_zfmisc_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_zfmisc_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(rc1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2)
          & v1_zfmisc_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_tex_2)).

fof(fc7_subset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : ~ v1_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_subset_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_20,plain,(
    ! [X40,X41] :
      ( ( ~ v2_struct_0(X41)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X40)
        | v2_struct_0(X40)
        | ~ v7_struct_0(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ v1_tex_2(X41,X40)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X40)
        | v2_struct_0(X40)
        | ~ v7_struct_0(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).

fof(c_0_21,plain,(
    ! [X48,X49] :
      ( ( ~ v2_struct_0(k1_tex_2(X48,X49))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ m1_subset_1(X49,u1_struct_0(X48)) )
      & ( v1_pre_topc(k1_tex_2(X48,X49))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ m1_subset_1(X49,u1_struct_0(X48)) )
      & ( m1_pre_topc(k1_tex_2(X48,X49),X48)
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ m1_subset_1(X49,u1_struct_0(X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_22,plain,(
    ! [X56,X57] :
      ( v2_struct_0(X56)
      | ~ l1_struct_0(X56)
      | ~ m1_subset_1(X57,u1_struct_0(X56))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X56),X57),u1_struct_0(X56))
      | ~ v7_struct_0(X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ( ~ v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) )
    & ( v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_24,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v1_tex_2(X43,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | X44 != u1_struct_0(X43)
        | v1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_pre_topc(X43,X42)
        | ~ l1_pre_topc(X42) )
      & ( m1_subset_1(esk3_2(X42,X43),k1_zfmisc_1(u1_struct_0(X42)))
        | v1_tex_2(X43,X42)
        | ~ m1_pre_topc(X43,X42)
        | ~ l1_pre_topc(X42) )
      & ( esk3_2(X42,X43) = u1_struct_0(X43)
        | v1_tex_2(X43,X42)
        | ~ m1_pre_topc(X43,X42)
        | ~ l1_pre_topc(X42) )
      & ( ~ v1_subset_1(esk3_2(X42,X43),u1_struct_0(X42))
        | v1_tex_2(X43,X42)
        | ~ m1_pre_topc(X43,X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_25,plain,(
    ! [X46,X47] :
      ( ( ~ v1_subset_1(X47,X46)
        | X47 != X46
        | ~ m1_subset_1(X47,k1_zfmisc_1(X46)) )
      & ( X47 = X46
        | v1_subset_1(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X46)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | ~ v1_tex_2(k1_tex_2(X1,X2),X1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
    | ~ v7_struct_0(esk5_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_39,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | l1_struct_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_40,plain,(
    ! [X38] :
      ( v7_struct_0(X38)
      | ~ l1_struct_0(X38)
      | ~ v1_zfmisc_1(u1_struct_0(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

fof(c_0_41,plain,(
    ! [X39] :
      ( ~ v7_struct_0(X39)
      | ~ l1_struct_0(X39)
      | v1_zfmisc_1(u1_struct_0(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

fof(c_0_42,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | l1_pre_topc(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_43,plain,(
    ! [X54,X55] :
      ( v1_xboole_0(X54)
      | v1_zfmisc_1(X54)
      | ~ m1_subset_1(X55,X54)
      | v1_subset_1(k6_domain_1(X54,X55),X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

cnf(c_0_44,plain,
    ( esk3_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,plain,
    ( esk3_2(X1,X2) = u1_struct_0(X1)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( ~ v7_struct_0(esk5_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_31])]),c_0_32])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_50,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_51,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X50,X51] :
      ( ( ~ v2_struct_0(k1_tex_2(X50,X51))
        | v2_struct_0(X50)
        | ~ l1_pre_topc(X50)
        | ~ m1_subset_1(X51,u1_struct_0(X50)) )
      & ( v7_struct_0(k1_tex_2(X50,X51))
        | v2_struct_0(X50)
        | ~ l1_pre_topc(X50)
        | ~ m1_subset_1(X51,u1_struct_0(X50)) )
      & ( v1_pre_topc(k1_tex_2(X50,X51))
        | v2_struct_0(X50)
        | ~ l1_pre_topc(X50)
        | ~ m1_subset_1(X51,u1_struct_0(X50)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_53,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( ~ v7_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_38])])).

cnf(c_0_58,plain,
    ( v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

fof(c_0_59,plain,(
    ! [X33,X34] :
      ( ~ v1_zfmisc_1(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | v1_zfmisc_1(X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_funct_1])])])).

fof(c_0_60,plain,(
    ! [X27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X27)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_61,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_62,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_47])).

cnf(c_0_65,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_31])])).

cnf(c_0_68,plain,
    ( u1_struct_0(k1_tex_2(X1,X2)) = u1_struct_0(X1)
    | v1_tex_2(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_38])])).

cnf(c_0_70,plain,
    ( v1_zfmisc_1(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_72,plain,(
    ! [X52] :
      ( ( m1_subset_1(esk4_1(X52),k1_zfmisc_1(X52))
        | v1_xboole_0(X52) )
      & ( ~ v1_xboole_0(esk4_1(X52))
        | v1_xboole_0(X52) )
      & ( v1_zfmisc_1(esk4_1(X52))
        | v1_xboole_0(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_tex_2])])])])])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk5_0,esk6_0)) = u1_struct_0(esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_38]),c_0_31])]),c_0_69]),c_0_32])).

fof(c_0_77,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] : ~ v1_xboole_0(k6_enumset1(X19,X20,X21,X22,X23,X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_subset_1])])).

cnf(c_0_78,plain,
    ( v1_zfmisc_1(k1_xboole_0)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,plain,
    ( v1_zfmisc_1(esk4_1(X1))
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_38]),c_0_31])]),c_0_32]),c_0_69])).

cnf(c_0_82,plain,
    ( ~ v1_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( v1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( v1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_zfmisc_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_84]),c_0_69])).

cnf(c_0_87,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_85,c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.13/0.39  fof(cc10_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(~(v2_struct_0(X2))=>(~(v2_struct_0(X2))&~(v1_tex_2(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 0.13/0.39  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.13/0.39  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 0.13/0.39  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.13/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.39  fof(fc6_struct_0, axiom, ![X1]:((~(v7_struct_0(X1))&l1_struct_0(X1))=>~(v1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 0.13/0.39  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.13/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.39  fof(t7_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 0.13/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.13/0.39  fof(cc5_funct_1, axiom, ![X1]:(v1_zfmisc_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_1)).
% 0.13/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(rc1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_xboole_0(X2)))&v1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_tex_2)).
% 0.13/0.39  fof(fc7_subset_1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:~(v1_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_subset_1)).
% 0.13/0.39  fof(c_0_19, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.13/0.39  fof(c_0_20, plain, ![X40, X41]:((~v2_struct_0(X41)|v2_struct_0(X41)|~m1_pre_topc(X41,X40)|(v2_struct_0(X40)|~v7_struct_0(X40)|~l1_pre_topc(X40)))&(~v1_tex_2(X41,X40)|v2_struct_0(X41)|~m1_pre_topc(X41,X40)|(v2_struct_0(X40)|~v7_struct_0(X40)|~l1_pre_topc(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).
% 0.13/0.39  fof(c_0_21, plain, ![X48, X49]:(((~v2_struct_0(k1_tex_2(X48,X49))|(v2_struct_0(X48)|~l1_pre_topc(X48)|~m1_subset_1(X49,u1_struct_0(X48))))&(v1_pre_topc(k1_tex_2(X48,X49))|(v2_struct_0(X48)|~l1_pre_topc(X48)|~m1_subset_1(X49,u1_struct_0(X48)))))&(m1_pre_topc(k1_tex_2(X48,X49),X48)|(v2_struct_0(X48)|~l1_pre_topc(X48)|~m1_subset_1(X49,u1_struct_0(X48))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.13/0.39  fof(c_0_22, plain, ![X56, X57]:(v2_struct_0(X56)|~l1_struct_0(X56)|(~m1_subset_1(X57,u1_struct_0(X56))|(~v1_subset_1(k6_domain_1(u1_struct_0(X56),X57),u1_struct_0(X56))|~v7_struct_0(X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.13/0.39  fof(c_0_23, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&((~v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)))&(v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.13/0.39  fof(c_0_24, plain, ![X42, X43, X44]:((~v1_tex_2(X43,X42)|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|(X44!=u1_struct_0(X43)|v1_subset_1(X44,u1_struct_0(X42))))|~m1_pre_topc(X43,X42)|~l1_pre_topc(X42))&((m1_subset_1(esk3_2(X42,X43),k1_zfmisc_1(u1_struct_0(X42)))|v1_tex_2(X43,X42)|~m1_pre_topc(X43,X42)|~l1_pre_topc(X42))&((esk3_2(X42,X43)=u1_struct_0(X43)|v1_tex_2(X43,X42)|~m1_pre_topc(X43,X42)|~l1_pre_topc(X42))&(~v1_subset_1(esk3_2(X42,X43),u1_struct_0(X42))|v1_tex_2(X43,X42)|~m1_pre_topc(X43,X42)|~l1_pre_topc(X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.13/0.39  fof(c_0_25, plain, ![X46, X47]:((~v1_subset_1(X47,X46)|X47!=X46|~m1_subset_1(X47,k1_zfmisc_1(X46)))&(X47=X46|v1_subset_1(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.39  cnf(c_0_26, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~v7_struct_0(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_27, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_28, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_29, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_33, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_34, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_35, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_36, plain, (v2_struct_0(X1)|~v1_tex_2(k1_tex_2(X1,X2),X1)|~v7_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|~v7_struct_0(esk5_0)|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])]), c_0_32])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  fof(c_0_39, plain, ![X35]:(~l1_pre_topc(X35)|l1_struct_0(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.39  fof(c_0_40, plain, ![X38]:(v7_struct_0(X38)|~l1_struct_0(X38)|~v1_zfmisc_1(u1_struct_0(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).
% 0.13/0.39  fof(c_0_41, plain, ![X39]:(~v7_struct_0(X39)|~l1_struct_0(X39)|v1_zfmisc_1(u1_struct_0(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.13/0.39  fof(c_0_42, plain, ![X36, X37]:(~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|l1_pre_topc(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.39  fof(c_0_43, plain, ![X54, X55]:(v1_xboole_0(X54)|v1_zfmisc_1(X54)|(~m1_subset_1(X55,X54)|v1_subset_1(k6_domain_1(X54,X55),X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).
% 0.13/0.39  cnf(c_0_44, plain, (esk3_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_45, plain, (esk3_2(X1,X2)=u1_struct_0(X1)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (~v7_struct_0(esk5_0)|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_31])]), c_0_32])).
% 0.13/0.39  cnf(c_0_47, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  cnf(c_0_48, plain, (v7_struct_0(X1)|~l1_struct_0(X1)|~v1_zfmisc_1(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.39  fof(c_0_49, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.39  fof(c_0_50, plain, ![X13, X14, X15, X16, X17]:((~r1_tarski(X13,X14)|(~r2_hidden(X15,X13)|r2_hidden(X15,X14)))&((r2_hidden(esk2_2(X16,X17),X16)|r1_tarski(X16,X17))&(~r2_hidden(esk2_2(X16,X17),X17)|r1_tarski(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  cnf(c_0_51, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  fof(c_0_52, plain, ![X50, X51]:(((~v2_struct_0(k1_tex_2(X50,X51))|(v2_struct_0(X50)|~l1_pre_topc(X50)|~m1_subset_1(X51,u1_struct_0(X50))))&(v7_struct_0(k1_tex_2(X50,X51))|(v2_struct_0(X50)|~l1_pre_topc(X50)|~m1_subset_1(X51,u1_struct_0(X50)))))&(v1_pre_topc(k1_tex_2(X50,X51))|(v2_struct_0(X50)|~l1_pre_topc(X50)|~m1_subset_1(X51,u1_struct_0(X50))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.13/0.39  cnf(c_0_53, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (~v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_55, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|v1_subset_1(k6_domain_1(X1,X2),X1)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_56, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (~v7_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_38])])).
% 0.13/0.39  cnf(c_0_58, plain, (v7_struct_0(X1)|~l1_pre_topc(X1)|~v1_zfmisc_1(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 0.13/0.39  fof(c_0_59, plain, ![X33, X34]:(~v1_zfmisc_1(X33)|(~m1_subset_1(X34,k1_zfmisc_1(X33))|v1_zfmisc_1(X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_funct_1])])])).
% 0.13/0.39  fof(c_0_60, plain, ![X27]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X27)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.39  fof(c_0_61, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  cnf(c_0_62, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.39  cnf(c_0_63, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.39  cnf(c_0_64, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_51, c_0_47])).
% 0.13/0.39  cnf(c_0_65, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.39  cnf(c_0_66, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_53, c_0_27])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))|~v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_31])])).
% 0.13/0.39  cnf(c_0_68, plain, (u1_struct_0(k1_tex_2(X1,X2))=u1_struct_0(X1)|v1_tex_2(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_27])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (~v1_zfmisc_1(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_38])])).
% 0.13/0.39  cnf(c_0_70, plain, (v1_zfmisc_1(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.39  cnf(c_0_71, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.39  fof(c_0_72, plain, ![X52]:(((m1_subset_1(esk4_1(X52),k1_zfmisc_1(X52))|v1_xboole_0(X52))&(~v1_xboole_0(esk4_1(X52))|v1_xboole_0(X52)))&(v1_zfmisc_1(esk4_1(X52))|v1_xboole_0(X52))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_tex_2])])])])])).
% 0.13/0.39  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.39  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.39  cnf(c_0_75, plain, (v2_struct_0(X1)|v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (u1_struct_0(k1_tex_2(esk5_0,esk6_0))=u1_struct_0(esk5_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_38]), c_0_31])]), c_0_69]), c_0_32])).
% 0.13/0.39  fof(c_0_77, plain, ![X19, X20, X21, X22, X23, X24, X25, X26]:~v1_xboole_0(k6_enumset1(X19,X20,X21,X22,X23,X24,X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_subset_1])])).
% 0.13/0.39  cnf(c_0_78, plain, (v1_zfmisc_1(k1_xboole_0)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.39  cnf(c_0_79, plain, (v1_zfmisc_1(esk4_1(X1))|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.39  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_38]), c_0_31])]), c_0_32]), c_0_69])).
% 0.13/0.39  cnf(c_0_82, plain, (~v1_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.13/0.39  cnf(c_0_83, plain, (v1_zfmisc_1(k1_xboole_0)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.13/0.39  cnf(c_0_85, plain, (v1_zfmisc_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.13/0.39  cnf(c_0_86, negated_conjecture, (~v1_zfmisc_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_84]), c_0_69])).
% 0.13/0.39  cnf(c_0_87, plain, ($false), inference(sr,[status(thm)],[c_0_85, c_0_86]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 88
% 0.13/0.39  # Proof object clause steps            : 49
% 0.13/0.39  # Proof object formula steps           : 39
% 0.13/0.39  # Proof object conjectures             : 17
% 0.13/0.39  # Proof object clause conjectures      : 14
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 26
% 0.13/0.39  # Proof object initial formulas used   : 19
% 0.13/0.39  # Proof object generating inferences   : 22
% 0.13/0.39  # Proof object simplifying inferences  : 28
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 20
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 39
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 38
% 0.13/0.39  # Processed clauses                    : 186
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 33
% 0.13/0.39  # ...remaining for further processing  : 153
% 0.13/0.39  # Other redundant clauses eliminated   : 1
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 7
% 0.13/0.39  # Backward-rewritten                   : 25
% 0.13/0.39  # Generated clauses                    : 221
% 0.13/0.39  # ...of the previous two non-trivial   : 206
% 0.13/0.39  # Contextual simplify-reflections      : 7
% 0.13/0.39  # Paramodulations                      : 218
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 1
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 82
% 0.13/0.39  #    Positive orientable unit clauses  : 9
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 6
% 0.13/0.39  #    Non-unit-clauses                  : 67
% 0.13/0.39  # Current number of unprocessed clauses: 72
% 0.13/0.39  # ...number of literals in the above   : 279
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 70
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 2205
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 891
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 45
% 0.13/0.39  # Unit Clause-clause subsumption calls : 208
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 15
% 0.13/0.39  # BW rewrite match successes           : 6
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 6676
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.037 s
% 0.13/0.39  # System time              : 0.008 s
% 0.13/0.39  # Total time               : 0.044 s
% 0.13/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
