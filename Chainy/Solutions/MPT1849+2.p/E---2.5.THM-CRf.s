%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1849+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 32.10s
% Output     : CNFRefutation 32.10s
% Verified   : 
% Statistics : Number of formulae       :  124 (6733 expanded)
%              Number of clauses        :   87 (2604 expanded)
%              Number of leaves         :   18 (1639 expanded)
%              Depth                    :   15
%              Number of atoms          :  292 (24152 expanded)
%              Number of equality atoms :   57 (3673 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_tex_2(X2,X1)
            & m1_pre_topc(X2,X1) )
         => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',dt_m1_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t2_tsep_1)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t11_tmap_1)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',t65_pre_topc)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t35_borsuk_1)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',dt_l1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',dt_k1_pre_topc)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',d3_struct_0)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',t29_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',d10_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(fc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc7_pre_topc)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_tex_2(X2,X1)
              & m1_pre_topc(X2,X1) )
           => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t16_tex_2])).

fof(c_0_19,plain,(
    ! [X5918,X5919] :
      ( ~ l1_pre_topc(X5918)
      | ~ m1_pre_topc(X5919,X5918)
      | l1_pre_topc(X5919) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1328_0)
    & l1_pre_topc(esk1328_0)
    & ~ v1_tex_2(esk1329_0,esk1328_0)
    & m1_pre_topc(esk1329_0,esk1328_0)
    & g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0)) != g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_21,plain,(
    ! [X11139] :
      ( ~ l1_pre_topc(X11139)
      | m1_pre_topc(X11139,X11139) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_22,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk1329_0,esk1328_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1328_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X10838,X10839] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X10839),u1_pre_topc(X10839)))
        | ~ m1_pre_topc(X10839,X10838)
        | ~ l1_pre_topc(X10838) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X10839),u1_pre_topc(X10839)),X10838)
        | ~ m1_pre_topc(X10839,X10838)
        | ~ l1_pre_topc(X10838) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1329_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

fof(c_0_28,plain,(
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

fof(c_0_29,plain,(
    ! [X11166,X11167] :
      ( ~ l1_pre_topc(X11166)
      | ~ m1_pre_topc(X11167,X11166)
      | r1_tarski(u1_struct_0(X11167),u1_struct_0(X11166)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_30,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk1329_0,esk1329_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X2019,X2020] :
      ( ( ~ m1_subset_1(X2019,k1_zfmisc_1(X2020))
        | r1_tarski(X2019,X2020) )
      & ( ~ r1_tarski(X2019,X2020)
        | m1_subset_1(X2019,k1_zfmisc_1(X2020)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_34,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X11612,X11613,X11614] :
      ( ( ~ v1_tex_2(X11613,X11612)
        | ~ m1_subset_1(X11614,k1_zfmisc_1(u1_struct_0(X11612)))
        | X11614 != u1_struct_0(X11613)
        | v1_subset_1(X11614,u1_struct_0(X11612))
        | ~ m1_pre_topc(X11613,X11612)
        | ~ l1_pre_topc(X11612) )
      & ( m1_subset_1(esk1302_2(X11612,X11613),k1_zfmisc_1(u1_struct_0(X11612)))
        | v1_tex_2(X11613,X11612)
        | ~ m1_pre_topc(X11613,X11612)
        | ~ l1_pre_topc(X11612) )
      & ( esk1302_2(X11612,X11613) = u1_struct_0(X11613)
        | v1_tex_2(X11613,X11612)
        | ~ m1_pre_topc(X11613,X11612)
        | ~ l1_pre_topc(X11612) )
      & ( ~ v1_subset_1(esk1302_2(X11612,X11613),u1_struct_0(X11612))
        | v1_tex_2(X11613,X11612)
        | ~ m1_pre_topc(X11613,X11612)
        | ~ l1_pre_topc(X11612) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_36,plain,(
    ! [X5917] :
      ( ~ l1_pre_topc(X5917)
      | l1_struct_0(X5917) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0)),esk1329_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_27])])).

fof(c_0_38,plain,(
    ! [X112,X113] :
      ( ( r1_tarski(X112,X113)
        | X112 != X113 )
      & ( r1_tarski(X113,X112)
        | X112 != X113 )
      & ( ~ r1_tarski(X112,X113)
        | ~ r1_tarski(X113,X112)
        | X112 = X113 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_32,c_0_22])).

fof(c_0_40,plain,(
    ! [X5911,X5912] :
      ( ( v1_pre_topc(k1_pre_topc(X5911,X5912))
        | ~ l1_pre_topc(X5911)
        | ~ m1_subset_1(X5912,k1_zfmisc_1(u1_struct_0(X5911))) )
      & ( m1_pre_topc(k1_pre_topc(X5911,X5912),X5911)
        | ~ l1_pre_topc(X5911)
        | ~ m1_subset_1(X5912,k1_zfmisc_1(u1_struct_0(X5911))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1329_0),u1_struct_0(esk1328_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_24])])).

fof(c_0_43,plain,(
    ! [X11616,X11617] :
      ( ( ~ v1_subset_1(X11617,X11616)
        | X11617 != X11616
        | ~ m1_subset_1(X11617,k1_zfmisc_1(X11616)) )
      & ( X11617 = X11616
        | v1_subset_1(X11617,X11616)
        | ~ m1_subset_1(X11617,k1_zfmisc_1(X11616)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_44,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1302_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_tex_2(esk1329_0,esk1328_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,plain,
    ( esk1302_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_47,plain,(
    ! [X5896] :
      ( ~ l1_struct_0(X5896)
      | k2_struct_0(X5896) = u1_struct_0(X5896) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_48,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_37]),c_0_27])])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))),u1_struct_0(esk1329_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_37]),c_0_27])])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk1329_0,g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_31]),c_0_27])])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk1328_0,esk1328_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_54,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1329_0),k1_zfmisc_1(u1_struct_0(esk1328_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_56,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_subset_1(esk1302_2(esk1328_0,esk1329_0),u1_struct_0(esk1328_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_23]),c_0_24])]),c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( esk1302_2(esk1328_0,esk1329_0) = u1_struct_0(esk1329_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_23]),c_0_24])]),c_0_45])).

cnf(c_0_59,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))) = u1_struct_0(esk1329_0)
    | ~ r1_tarski(u1_struct_0(esk1329_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1329_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_52]),c_0_49])])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)),esk1328_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_53]),c_0_24])])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk1328_0,u1_struct_0(esk1329_0)),esk1328_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_24])])).

fof(c_0_65,plain,(
    ! [X5996,X5997] :
      ( ~ l1_pre_topc(X5996)
      | ~ m1_subset_1(X5997,k1_zfmisc_1(u1_struct_0(X5996)))
      | u1_struct_0(k1_pre_topc(X5996,X5997)) = X5997 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_66,plain,(
    ! [X5871,X5872,X5873] :
      ( ( X5873 != k1_pre_topc(X5871,X5872)
        | k2_struct_0(X5873) = X5872
        | ~ v1_pre_topc(X5873)
        | ~ m1_pre_topc(X5873,X5871)
        | ~ m1_subset_1(X5872,k1_zfmisc_1(u1_struct_0(X5871)))
        | ~ l1_pre_topc(X5871) )
      & ( k2_struct_0(X5873) != X5872
        | X5873 = k1_pre_topc(X5871,X5872)
        | ~ v1_pre_topc(X5873)
        | ~ m1_pre_topc(X5873,X5871)
        | ~ m1_subset_1(X5872,k1_zfmisc_1(u1_struct_0(X5871)))
        | ~ l1_pre_topc(X5871) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk1329_0) = u1_struct_0(esk1328_0)
    | v1_subset_1(u1_struct_0(esk1329_0),u1_struct_0(esk1328_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk1329_0),u1_struct_0(esk1328_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))) = u1_struct_0(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))) = u1_struct_0(esk1329_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_71,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_72,plain,(
    ! [X1583] : m1_subset_1(k2_subset_1(X1583),k1_zfmisc_1(X1583)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_73,plain,(
    ! [X1539] : k2_subset_1(X1539) = X1539 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_63]),c_0_24])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))),u1_struct_0(esk1328_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_63]),c_0_24])])).

cnf(c_0_76,negated_conjecture,
    ( m1_pre_topc(esk1328_0,g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_53]),c_0_24])])).

fof(c_0_77,plain,(
    ! [X5941] :
      ( ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X5941),u1_pre_topc(X5941)))
        | v2_struct_0(X5941)
        | ~ l1_pre_topc(X5941) )
      & ( v1_pre_topc(g1_pre_topc(u1_struct_0(X5941),u1_pre_topc(X5941)))
        | v2_struct_0(X5941)
        | ~ l1_pre_topc(X5941) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).

cnf(c_0_78,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk1328_0,u1_struct_0(esk1329_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_64]),c_0_24])])).

cnf(c_0_79,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_80,plain,
    ( X1 = k1_pre_topc(X3,X2)
    | k2_struct_0(X1) != X2
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(esk1329_0) = u1_struct_0(esk1328_0) ),
    inference(sr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))) = u1_struct_0(esk1329_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_31]),c_0_27])])).

cnf(c_0_84,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_85,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_86,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0)),esk1328_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_24])])).

cnf(c_0_87,negated_conjecture,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_74])).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) = u1_struct_0(esk1328_0)
    | ~ r1_tarski(u1_struct_0(esk1328_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_75])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1328_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_76]),c_0_74])])).

cnf(c_0_90,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_91,negated_conjecture,
    ( ~ v2_struct_0(esk1328_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_92,negated_conjecture,
    ( l1_struct_0(k1_pre_topc(esk1328_0,u1_struct_0(esk1329_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_78])).

cnf(c_0_93,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk1328_0,u1_struct_0(esk1329_0))) = u1_struct_0(esk1329_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_55]),c_0_24])])).

cnf(c_0_94,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_95,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0)) != g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_96,plain,
    ( k1_pre_topc(X1,k2_struct_0(X2)) = X2
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_97,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1329_0)),esk1329_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_81])).

cnf(c_0_98,negated_conjecture,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1329_0))) = u1_struct_0(esk1328_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_81]),c_0_81])).

cnf(c_0_99,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1329_0))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_81])).

cnf(c_0_100,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_101,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1329_0),u1_pre_topc(esk1329_0)),g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_86]),c_0_24])])).

cnf(c_0_102,negated_conjecture,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) = u1_struct_0(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_87])).

cnf(c_0_103,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) = u1_struct_0(esk1328_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])])).

cnf(c_0_104,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_24]),c_0_91])).

cnf(c_0_105,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk1328_0,u1_struct_0(esk1329_0)),k1_pre_topc(esk1328_0,u1_struct_0(esk1329_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_78])).

cnf(c_0_106,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk1328_0,u1_struct_0(esk1329_0))) = u1_struct_0(esk1329_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_92]),c_0_93])).

cnf(c_0_107,negated_conjecture,
    ( v1_pre_topc(k1_pre_topc(esk1328_0,u1_struct_0(esk1329_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_55]),c_0_24])])).

cnf(c_0_108,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1329_0)) != g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)) ),
    inference(rw,[status(thm)],[c_0_95,c_0_81])).

cnf(c_0_109,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1329_0)) = k1_pre_topc(esk1329_0,u1_struct_0(esk1328_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_99]),c_0_27]),c_0_98]),c_0_81]),c_0_100])])).

cnf(c_0_110,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1329_0)),g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0))) ),
    inference(rw,[status(thm)],[c_0_101,c_0_81])).

cnf(c_0_111,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)) = k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_63]),c_0_102]),c_0_103]),c_0_104]),c_0_24]),c_0_102]),c_0_103]),c_0_100])])).

cnf(c_0_112,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0)),k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_81]),c_0_81])).

cnf(c_0_113,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0))) = u1_struct_0(esk1328_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_81]),c_0_81])).

cnf(c_0_114,negated_conjecture,
    ( v1_pre_topc(k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0))) ),
    inference(rw,[status(thm)],[c_0_107,c_0_81])).

cnf(c_0_115,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0))) ),
    inference(rw,[status(thm)],[c_0_78,c_0_81])).

cnf(c_0_116,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0))) = u1_struct_0(esk1328_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_81]),c_0_81])).

cnf(c_0_117,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1328_0),u1_pre_topc(esk1328_0)) != k1_pre_topc(esk1329_0,u1_struct_0(esk1328_0)) ),
    inference(rw,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_118,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk1329_0,u1_struct_0(esk1328_0)),k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_109]),c_0_111])).

cnf(c_0_119,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk1329_0,u1_struct_0(esk1328_0))) = u1_struct_0(esk1328_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_109])).

cnf(c_0_120,negated_conjecture,
    ( v1_pre_topc(k1_pre_topc(esk1329_0,u1_struct_0(esk1328_0))) ),
    inference(rw,[status(thm)],[c_0_99,c_0_109])).

cnf(c_0_121,negated_conjecture,
    ( k1_pre_topc(k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0)),u1_struct_0(esk1328_0)) = k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_112]),c_0_113]),c_0_114]),c_0_115]),c_0_113]),c_0_116]),c_0_100])])).

cnf(c_0_122,negated_conjecture,
    ( k1_pre_topc(esk1329_0,u1_struct_0(esk1328_0)) != k1_pre_topc(esk1328_0,u1_struct_0(esk1328_0)) ),
    inference(rw,[status(thm)],[c_0_117,c_0_111])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_118]),c_0_119]),c_0_120]),c_0_115]),c_0_119]),c_0_116]),c_0_100])]),c_0_121]),c_0_122]),
    [proof]).
%------------------------------------------------------------------------------
