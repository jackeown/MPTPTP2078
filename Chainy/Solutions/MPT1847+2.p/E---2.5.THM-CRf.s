%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1847+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 16.34s
% Output     : CNFRefutation 16.34s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 231 expanded)
%              Number of clauses        :   44 (  88 expanded)
%              Number of leaves         :   13 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  191 ( 905 expanded)
%              Number of equality atoms :   26 ( 117 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',dt_m1_pre_topc)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',t65_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t2_tsep_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',t59_pre_topc)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t35_borsuk_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t1_tsep_1)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',fc14_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X5918,X5919] :
      ( ~ l1_pre_topc(X5918)
      | ~ m1_pre_topc(X5919,X5918)
      | l1_pre_topc(X5919) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1327_0)
    & m1_pre_topc(esk1328_0,esk1327_0)
    & m1_pre_topc(esk1329_0,esk1327_0)
    & g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)) = g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))
    & v1_tex_2(esk1328_0,esk1327_0)
    & ~ v1_tex_2(esk1329_0,esk1327_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X6086,X6087] :
      ( ( ~ m1_pre_topc(X6086,X6087)
        | m1_pre_topc(X6086,g1_pre_topc(u1_struct_0(X6087),u1_pre_topc(X6087)))
        | ~ l1_pre_topc(X6087)
        | ~ l1_pre_topc(X6086) )
      & ( ~ m1_pre_topc(X6086,g1_pre_topc(u1_struct_0(X6087),u1_pre_topc(X6087)))
        | m1_pre_topc(X6086,X6087)
        | ~ l1_pre_topc(X6087)
        | ~ l1_pre_topc(X6086) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_17,plain,(
    ! [X11139] :
      ( ~ l1_pre_topc(X11139)
      | m1_pre_topc(X11139,X11139) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_18,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(esk1329_0,esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1329_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk1328_0,esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X6067,X6068] :
      ( ~ l1_pre_topc(X6067)
      | ~ m1_pre_topc(X6068,g1_pre_topc(u1_struct_0(X6067),u1_pre_topc(X6067)))
      | m1_pre_topc(X6068,X6067) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk1329_0,esk1329_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)) = g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk1328_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_24]),c_0_20])])).

fof(c_0_30,plain,(
    ! [X11166,X11167] :
      ( ~ l1_pre_topc(X11166)
      | ~ m1_pre_topc(X11167,X11166)
      | r1_tarski(u1_struct_0(X11167),u1_struct_0(X11166)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_31,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk1329_0,g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_23])])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk1328_0,esk1328_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_29])).

fof(c_0_34,plain,(
    ! [X112,X113] :
      ( ( r1_tarski(X112,X113)
        | X112 != X113 )
      & ( r1_tarski(X113,X112)
        | X112 != X113 )
      & ( ~ r1_tarski(X112,X113)
        | ~ r1_tarski(X113,X112)
        | X112 = X113 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_35,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk1329_0,esk1328_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(X1,esk1329_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_23])])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk1328_0,g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_33]),c_0_29])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1329_0),u1_struct_0(esk1328_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29])])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk1328_0,esk1329_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X2019,X2020] :
      ( ( ~ m1_subset_1(X2019,k1_zfmisc_1(X2020))
        | r1_tarski(X2019,X2020) )
      & ( ~ r1_tarski(X2019,X2020)
        | m1_subset_1(X2019,k1_zfmisc_1(X2020)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_43,plain,(
    ! [X11604,X11605,X11606] :
      ( ( ~ v1_tex_2(X11605,X11604)
        | ~ m1_subset_1(X11606,k1_zfmisc_1(u1_struct_0(X11604)))
        | X11606 != u1_struct_0(X11605)
        | v1_subset_1(X11606,u1_struct_0(X11604))
        | ~ m1_pre_topc(X11605,X11604)
        | ~ l1_pre_topc(X11604) )
      & ( m1_subset_1(esk1302_2(X11604,X11605),k1_zfmisc_1(u1_struct_0(X11604)))
        | v1_tex_2(X11605,X11604)
        | ~ m1_pre_topc(X11605,X11604)
        | ~ l1_pre_topc(X11604) )
      & ( esk1302_2(X11604,X11605) = u1_struct_0(X11605)
        | v1_tex_2(X11605,X11604)
        | ~ m1_pre_topc(X11605,X11604)
        | ~ l1_pre_topc(X11604) )
      & ( ~ v1_subset_1(esk1302_2(X11604,X11605),u1_struct_0(X11604))
        | v1_tex_2(X11605,X11604)
        | ~ m1_pre_topc(X11605,X11604)
        | ~ l1_pre_topc(X11604) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk1329_0) = u1_struct_0(esk1328_0)
    | ~ r1_tarski(u1_struct_0(esk1328_0),u1_struct_0(esk1329_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1328_0),u1_struct_0(esk1329_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_41]),c_0_23])])).

fof(c_0_46,plain,(
    ! [X11608,X11609] :
      ( ( ~ v1_subset_1(X11609,X11608)
        | X11609 != X11608
        | ~ m1_subset_1(X11609,k1_zfmisc_1(X11608)) )
      & ( X11609 = X11608
        | v1_subset_1(X11609,X11608)
        | ~ m1_subset_1(X11609,k1_zfmisc_1(X11608)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1328_0),u1_struct_0(esk1327_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_20])])).

cnf(c_0_49,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1302_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_tex_2(esk1329_0,esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,plain,
    ( esk1302_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk1329_0) = u1_struct_0(esk1328_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

fof(c_0_53,plain,(
    ! [X11076,X11077] :
      ( ~ l1_pre_topc(X11076)
      | ~ m1_pre_topc(X11077,X11076)
      | m1_subset_1(u1_struct_0(X11077),k1_zfmisc_1(u1_struct_0(X11076))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1328_0),k1_zfmisc_1(u1_struct_0(esk1327_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_subset_1(esk1302_2(esk1327_0,esk1329_0),u1_struct_0(esk1327_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_19]),c_0_20])]),c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( esk1302_2(esk1327_0,esk1329_0) = u1_struct_0(esk1328_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_52]),c_0_20])]),c_0_50])).

fof(c_0_58,plain,(
    ! [X1956] : ~ v1_subset_1(k2_subset_1(X1956),X1956) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

fof(c_0_59,plain,(
    ! [X1539] : k2_subset_1(X1539) = X1539 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_60,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_61,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk1328_0) = u1_struct_0(esk1327_0)
    | v1_subset_1(u1_struct_0(esk1328_0),u1_struct_0(esk1327_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk1328_0),u1_struct_0(esk1327_0)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_60]),c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk1328_0) = u1_struct_0(esk1327_0) ),
    inference(sr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( v1_tex_2(esk1328_0,esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_24]),c_0_67]),c_0_68]),c_0_20])]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
