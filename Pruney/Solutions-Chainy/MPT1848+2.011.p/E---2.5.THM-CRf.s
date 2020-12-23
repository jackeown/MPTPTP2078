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
% DateTime   : Thu Dec  3 11:19:21 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 119 expanded)
%              Number of clauses        :   21 (  53 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 271 expanded)
%              Number of equality atoms :   18 (  57 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(fc12_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

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

fof(c_0_8,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_9,plain,(
    ! [X7] :
      ( v1_orders_2(k2_yellow_1(X7))
      & l1_orders_2(k2_yellow_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_10,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | ~ v1_subset_1(k2_struct_0(X5),u1_struct_0(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).

fof(c_0_11,plain,(
    ! [X8] :
      ( u1_struct_0(k2_yellow_1(X8)) = X8
      & u1_orders_2(k2_yellow_1(X8)) = k1_yellow_1(X8) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_12,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | m1_subset_1(k2_struct_0(X4),k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_13,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( ~ l1_struct_0(X1)
    | ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_tex_2(X10,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | X11 != u1_struct_0(X10)
        | v1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_pre_topc(X10,X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk1_2(X9,X10),k1_zfmisc_1(u1_struct_0(X9)))
        | v1_tex_2(X10,X9)
        | ~ m1_pre_topc(X10,X9)
        | ~ l1_pre_topc(X9) )
      & ( esk1_2(X9,X10) = u1_struct_0(X10)
        | v1_tex_2(X10,X9)
        | ~ m1_pre_topc(X10,X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ v1_subset_1(esk1_2(X9,X10),u1_struct_0(X9))
        | v1_tex_2(X10,X9)
        | ~ m1_pre_topc(X10,X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
                & v1_tex_2(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_tex_2])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( ( ~ v1_subset_1(X14,X13)
        | X14 != X13
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) )
      & ( X14 = X13
        | v1_subset_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( l1_struct_0(k2_yellow_1(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1)
    | ~ l1_struct_0(k2_yellow_1(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    & v1_tex_2(esk3_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_25,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(k2_struct_0(k2_yellow_1(X1)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])).

cnf(c_0_27,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_21])])).

cnf(c_0_28,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k2_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ v1_tex_2(esk3_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( v1_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:32:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.14/0.37  # and selection function SelectLargestOrientable.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.37  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.14/0.37  fof(fc12_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>~(v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 0.14/0.37  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.14/0.37  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.14/0.37  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.14/0.37  fof(t15_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 0.14/0.37  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.14/0.37  fof(c_0_8, plain, ![X6]:(~l1_orders_2(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.37  fof(c_0_9, plain, ![X7]:(v1_orders_2(k2_yellow_1(X7))&l1_orders_2(k2_yellow_1(X7))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.14/0.37  fof(c_0_10, plain, ![X5]:(~l1_struct_0(X5)|~v1_subset_1(k2_struct_0(X5),u1_struct_0(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).
% 0.14/0.37  fof(c_0_11, plain, ![X8]:(u1_struct_0(k2_yellow_1(X8))=X8&u1_orders_2(k2_yellow_1(X8))=k1_yellow_1(X8)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.14/0.37  fof(c_0_12, plain, ![X4]:(~l1_struct_0(X4)|m1_subset_1(k2_struct_0(X4),k1_zfmisc_1(u1_struct_0(X4)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.14/0.37  cnf(c_0_13, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_14, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_15, plain, (~l1_struct_0(X1)|~v1_subset_1(k2_struct_0(X1),u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_16, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  fof(c_0_17, plain, ![X9, X10, X11]:((~v1_tex_2(X10,X9)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|(X11!=u1_struct_0(X10)|v1_subset_1(X11,u1_struct_0(X9))))|~m1_pre_topc(X10,X9)|~l1_pre_topc(X9))&((m1_subset_1(esk1_2(X9,X10),k1_zfmisc_1(u1_struct_0(X9)))|v1_tex_2(X10,X9)|~m1_pre_topc(X10,X9)|~l1_pre_topc(X9))&((esk1_2(X9,X10)=u1_struct_0(X10)|v1_tex_2(X10,X9)|~m1_pre_topc(X10,X9)|~l1_pre_topc(X9))&(~v1_subset_1(esk1_2(X9,X10),u1_struct_0(X9))|v1_tex_2(X10,X9)|~m1_pre_topc(X10,X9)|~l1_pre_topc(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.14/0.37  fof(c_0_18, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1)))))), inference(assume_negation,[status(cth)],[t15_tex_2])).
% 0.14/0.37  fof(c_0_19, plain, ![X13, X14]:((~v1_subset_1(X14,X13)|X14!=X13|~m1_subset_1(X14,k1_zfmisc_1(X13)))&(X14=X13|v1_subset_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.14/0.37  cnf(c_0_20, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_21, plain, (l1_struct_0(k2_yellow_1(X1))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.37  cnf(c_0_22, plain, (~v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1)|~l1_struct_0(k2_yellow_1(X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.37  cnf(c_0_23, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  fof(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_pre_topc(esk3_0,esk2_0)&(u1_struct_0(esk3_0)=u1_struct_0(esk2_0)&v1_tex_2(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.14/0.37  cnf(c_0_25, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.37  cnf(c_0_26, plain, (m1_subset_1(k2_struct_0(k2_yellow_1(X1)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_16])).
% 0.14/0.37  cnf(c_0_27, plain, (~v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_21])])).
% 0.14/0.37  cnf(c_0_28, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_30, plain, (k2_struct_0(k2_yellow_1(X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, (v1_subset_1(u1_struct_0(esk2_0),u1_struct_0(X1))|~v1_tex_2(esk3_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.37  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_26, c_0_30])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (v1_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_36, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_27, c_0_30])).
% 0.14/0.37  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 38
% 0.14/0.37  # Proof object clause steps            : 21
% 0.14/0.37  # Proof object formula steps           : 17
% 0.14/0.37  # Proof object conjectures             : 9
% 0.14/0.37  # Proof object clause conjectures      : 6
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 11
% 0.14/0.37  # Proof object initial formulas used   : 8
% 0.14/0.37  # Proof object generating inferences   : 6
% 0.14/0.37  # Proof object simplifying inferences  : 12
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 8
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 17
% 0.14/0.37  # Removed in clause preprocessing      : 1
% 0.14/0.37  # Initial clauses in saturation        : 16
% 0.14/0.37  # Processed clauses                    : 49
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 3
% 0.14/0.37  # ...remaining for further processing  : 46
% 0.14/0.37  # Other redundant clauses eliminated   : 2
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 4
% 0.14/0.37  # Generated clauses                    : 22
% 0.14/0.37  # ...of the previous two non-trivial   : 24
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 20
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 2
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 24
% 0.14/0.37  #    Positive orientable unit clauses  : 10
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 13
% 0.14/0.37  # Current number of unprocessed clauses: 5
% 0.14/0.37  # ...number of literals in the above   : 23
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 21
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 164
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 49
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.37  # Unit Clause-clause subsumption calls : 10
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 6
% 0.14/0.37  # BW rewrite match successes           : 3
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1539
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.028 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.032 s
% 0.14/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
