%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 209 expanded)
%              Number of clauses        :   27 (  95 expanded)
%              Number of leaves         :   10 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 457 expanded)
%              Number of equality atoms :   23 ( 141 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k1_yellow_1,axiom,(
    ! [X1] :
      ( v1_relat_2(k1_yellow_1(X1))
      & v4_relat_2(k1_yellow_1(X1))
      & v8_relat_2(k1_yellow_1(X1))
      & v1_partfun1(k1_yellow_1(X1),X1)
      & m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(fc12_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

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

fof(t15_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
              & v1_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(c_0_10,plain,(
    ! [X10] :
      ( v1_relat_2(k1_yellow_1(X10))
      & v4_relat_2(k1_yellow_1(X10))
      & v8_relat_2(k1_yellow_1(X10))
      & v1_partfun1(k1_yellow_1(X10),X10)
      & m1_subset_1(k1_yellow_1(X10),k1_zfmisc_1(k2_zfmisc_1(X10,X10))) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).

fof(c_0_11,plain,(
    ! [X11] :
      ( u1_struct_0(k2_yellow_1(X11)) = X11
      & u1_orders_2(k2_yellow_1(X11)) = k1_yellow_1(X11) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_12,plain,(
    ! [X9] : k2_yellow_1(X9) = g1_orders_2(X9,k1_yellow_1(X9)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ( v1_orders_2(g1_orders_2(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) )
      & ( l1_orders_2(g1_orders_2(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | l1_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_18,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_orders_2(k2_yellow_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,u1_orders_2(k2_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_21,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | ~ v1_subset_1(k2_struct_0(X5),u1_struct_0(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).

fof(c_0_22,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | m1_subset_1(k2_struct_0(X4),k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_23,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,plain,
    ( ~ l1_struct_0(X1)
    | ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_27,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_tex_2(X13,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != u1_struct_0(X13)
        | v1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk1_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v1_tex_2(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( esk1_2(X12,X13) = u1_struct_0(X13)
        | v1_tex_2(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ v1_subset_1(esk1_2(X12,X13),u1_struct_0(X12))
        | v1_tex_2(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
                & v1_tex_2(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_tex_2])).

fof(c_0_29,plain,(
    ! [X16,X17] :
      ( ( ~ v1_subset_1(X17,X16)
        | X17 != X16
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) )
      & ( X17 = X16
        | v1_subset_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( l1_struct_0(k2_yellow_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1)
    | ~ l1_struct_0(k2_yellow_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    & v1_tex_2(esk3_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_struct_0(k2_yellow_1(X1)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_26])).

cnf(c_0_37,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_31])])).

cnf(c_0_38,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k2_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ v1_tex_2(esk3_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( v1_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.13/0.37  # and selection function SelectLargestOrientable.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(dt_k1_yellow_1, axiom, ![X1]:((((v1_relat_2(k1_yellow_1(X1))&v4_relat_2(k1_yellow_1(X1)))&v8_relat_2(k1_yellow_1(X1)))&v1_partfun1(k1_yellow_1(X1),X1))&m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_1)).
% 0.13/0.37  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.13/0.37  fof(d1_yellow_1, axiom, ![X1]:k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow_1)).
% 0.13/0.37  fof(dt_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(v1_orders_2(g1_orders_2(X1,X2))&l1_orders_2(g1_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 0.13/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.37  fof(fc12_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>~(v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 0.13/0.37  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.13/0.37  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.13/0.37  fof(t15_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 0.13/0.37  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.37  fof(c_0_10, plain, ![X10]:((((v1_relat_2(k1_yellow_1(X10))&v4_relat_2(k1_yellow_1(X10)))&v8_relat_2(k1_yellow_1(X10)))&v1_partfun1(k1_yellow_1(X10),X10))&m1_subset_1(k1_yellow_1(X10),k1_zfmisc_1(k2_zfmisc_1(X10,X10)))), inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).
% 0.13/0.37  fof(c_0_11, plain, ![X11]:(u1_struct_0(k2_yellow_1(X11))=X11&u1_orders_2(k2_yellow_1(X11))=k1_yellow_1(X11)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.13/0.37  fof(c_0_12, plain, ![X9]:k2_yellow_1(X9)=g1_orders_2(X9,k1_yellow_1(X9)), inference(variable_rename,[status(thm)],[d1_yellow_1])).
% 0.13/0.37  fof(c_0_13, plain, ![X6, X7]:((v1_orders_2(g1_orders_2(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))&(l1_orders_2(g1_orders_2(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).
% 0.13/0.37  cnf(c_0_14, plain, (m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_15, plain, (u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_16, plain, (k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_17, plain, ![X8]:(~l1_orders_2(X8)|l1_struct_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.37  cnf(c_0_18, plain, (l1_orders_2(g1_orders_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_19, plain, (m1_subset_1(u1_orders_2(k2_yellow_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.37  cnf(c_0_20, plain, (k2_yellow_1(X1)=g1_orders_2(X1,u1_orders_2(k2_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.13/0.37  fof(c_0_21, plain, ![X5]:(~l1_struct_0(X5)|~v1_subset_1(k2_struct_0(X5),u1_struct_0(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).
% 0.13/0.37  fof(c_0_22, plain, ![X4]:(~l1_struct_0(X4)|m1_subset_1(k2_struct_0(X4),k1_zfmisc_1(u1_struct_0(X4)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.13/0.37  cnf(c_0_23, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_24, plain, (l1_orders_2(k2_yellow_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.13/0.37  cnf(c_0_25, plain, (~l1_struct_0(X1)|~v1_subset_1(k2_struct_0(X1),u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_26, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  fof(c_0_27, plain, ![X12, X13, X14]:((~v1_tex_2(X13,X12)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(X14!=u1_struct_0(X13)|v1_subset_1(X14,u1_struct_0(X12))))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&((m1_subset_1(esk1_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v1_tex_2(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&((esk1_2(X12,X13)=u1_struct_0(X13)|v1_tex_2(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&(~v1_subset_1(esk1_2(X12,X13),u1_struct_0(X12))|v1_tex_2(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.13/0.37  fof(c_0_28, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1)))))), inference(assume_negation,[status(cth)],[t15_tex_2])).
% 0.13/0.37  fof(c_0_29, plain, ![X16, X17]:((~v1_subset_1(X17,X16)|X17!=X16|~m1_subset_1(X17,k1_zfmisc_1(X16)))&(X17=X16|v1_subset_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.37  cnf(c_0_30, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_31, plain, (l1_struct_0(k2_yellow_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_32, plain, (~v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1)|~l1_struct_0(k2_yellow_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.37  cnf(c_0_33, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  fof(c_0_34, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_pre_topc(esk3_0,esk2_0)&(u1_struct_0(esk3_0)=u1_struct_0(esk2_0)&v1_tex_2(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.13/0.37  cnf(c_0_35, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_36, plain, (m1_subset_1(k2_struct_0(k2_yellow_1(X1)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_26])).
% 0.13/0.37  cnf(c_0_37, plain, (~v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_31])])).
% 0.13/0.37  cnf(c_0_38, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_33])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_40, plain, (k2_struct_0(k2_yellow_1(X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (v1_subset_1(u1_struct_0(esk2_0),u1_struct_0(X1))|~v1_tex_2(esk3_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.37  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_36, c_0_40])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (v1_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_46, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_37, c_0_40])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45])]), c_0_46]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 48
% 0.13/0.37  # Proof object clause steps            : 27
% 0.13/0.37  # Proof object formula steps           : 21
% 0.13/0.37  # Proof object conjectures             : 9
% 0.13/0.37  # Proof object clause conjectures      : 6
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 14
% 0.13/0.37  # Proof object initial formulas used   : 10
% 0.13/0.37  # Proof object generating inferences   : 7
% 0.13/0.37  # Proof object simplifying inferences  : 15
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 10
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 23
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 22
% 0.13/0.37  # Processed clauses                    : 71
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 4
% 0.13/0.37  # ...remaining for further processing  : 67
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 4
% 0.13/0.37  # Generated clauses                    : 50
% 0.13/0.37  # ...of the previous two non-trivial   : 42
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 48
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 2
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 39
% 0.13/0.37  #    Positive orientable unit clauses  : 20
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 18
% 0.13/0.37  # Current number of unprocessed clauses: 11
% 0.13/0.37  # ...number of literals in the above   : 35
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 27
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 117
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 30
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 13
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 7
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2346
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.028 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
