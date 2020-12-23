%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:16 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 322 expanded)
%              Number of clauses        :   30 ( 113 expanded)
%              Number of leaves         :    6 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 (1710 expanded)
%              Number of equality atoms :   30 ( 261 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(rc2_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v3_pre_topc(X2,X1)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_tops_1)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t106_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(c_0_6,plain,(
    ! [X3,X4] :
      ( ( ~ v3_pre_topc(X4,X3)
        | r2_hidden(X4,u1_pre_topc(X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3) )
      & ( ~ r2_hidden(X4,u1_pre_topc(X3))
        | v3_pre_topc(X4,X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_7,plain,(
    ! [X5] :
      ( ( m1_subset_1(esk1_1(X5),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v3_pre_topc(esk1_1(X5),X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v4_pre_topc(esk1_1(X5),X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc2_tops_1])])])])).

fof(c_0_8,plain,(
    ! [X7,X8] :
      ( v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | k6_tmap_1(X7,X8) = g1_pre_topc(u1_struct_0(X7),k5_tmap_1(X7,X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ( ~ r2_hidden(X10,u1_pre_topc(X9))
        | u1_pre_topc(X9) = k5_tmap_1(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( u1_pre_topc(X9) != k5_tmap_1(X9,X10)
        | r2_hidden(X10,u1_pre_topc(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v3_pre_topc(esk1_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ( u1_struct_0(k6_tmap_1(X11,X12)) = u1_struct_0(X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( u1_pre_topc(k6_tmap_1(X11,X12)) = k5_tmap_1(X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_1(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tmap_1])).

cnf(c_0_18,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,esk1_1(X1))) = k6_tmap_1(X1,esk1_1(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_11])).

cnf(c_0_20,plain,
    ( k5_tmap_1(X1,esk1_1(X1)) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_11])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k6_tmap_1(esk2_0,esk3_0) )
    & ( v3_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_22,plain,
    ( u1_pre_topc(k6_tmap_1(X1,esk1_1(X1))) = k5_tmap_1(X1,esk1_1(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_23,plain,
    ( k6_tmap_1(X1,esk1_1(X1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = k5_tmap_1(X1,esk1_1(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k6_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) = k5_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k5_tmap_1(esk2_0,esk1_1(esk2_0)) = k5_tmap_1(esk2_0,esk3_0)
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( k5_tmap_1(esk2_0,esk3_0) = u1_pre_topc(esk2_0)
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_31]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_24]),c_0_26])])).

cnf(c_0_35,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_0,u1_pre_topc(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_24]),c_0_26])]),c_0_27]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k6_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_24]),c_0_26])])).

cnf(c_0_39,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,esk3_0)) = k6_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( k5_tmap_1(esk2_0,esk3_0) = u1_pre_topc(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_36]),c_0_25]),c_0_24]),c_0_26])]),c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k6_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:06:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.18/0.37  # and selection function SelectNewComplexAHP.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.027 s
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.18/0.37  fof(rc2_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X2,X1))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_tops_1)).
% 0.18/0.37  fof(d9_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 0.18/0.37  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.18/0.37  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.18/0.37  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.18/0.37  fof(c_0_6, plain, ![X3, X4]:((~v3_pre_topc(X4,X3)|r2_hidden(X4,u1_pre_topc(X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(X3))&(~r2_hidden(X4,u1_pre_topc(X3))|v3_pre_topc(X4,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(X3))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.18/0.37  fof(c_0_7, plain, ![X5]:(((m1_subset_1(esk1_1(X5),k1_zfmisc_1(u1_struct_0(X5)))|(~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(v3_pre_topc(esk1_1(X5),X5)|(~v2_pre_topc(X5)|~l1_pre_topc(X5))))&(v4_pre_topc(esk1_1(X5),X5)|(~v2_pre_topc(X5)|~l1_pre_topc(X5)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc2_tops_1])])])])).
% 0.18/0.37  fof(c_0_8, plain, ![X7, X8]:(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|k6_tmap_1(X7,X8)=g1_pre_topc(u1_struct_0(X7),k5_tmap_1(X7,X8)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).
% 0.18/0.37  fof(c_0_9, plain, ![X9, X10]:((~r2_hidden(X10,u1_pre_topc(X9))|u1_pre_topc(X9)=k5_tmap_1(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)))&(u1_pre_topc(X9)!=k5_tmap_1(X9,X10)|r2_hidden(X10,u1_pre_topc(X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.18/0.37  cnf(c_0_10, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.37  cnf(c_0_11, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.37  cnf(c_0_12, plain, (v3_pre_topc(esk1_1(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.37  fof(c_0_13, plain, ![X11, X12]:((u1_struct_0(k6_tmap_1(X11,X12))=u1_struct_0(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)))&(u1_pre_topc(k6_tmap_1(X11,X12))=k5_tmap_1(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.18/0.37  cnf(c_0_14, plain, (v2_struct_0(X1)|k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_15, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_16, plain, (r2_hidden(esk1_1(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.18/0.37  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.18/0.37  cnf(c_0_18, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.37  cnf(c_0_19, plain, (g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,esk1_1(X1)))=k6_tmap_1(X1,esk1_1(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_14, c_0_11])).
% 0.18/0.37  cnf(c_0_20, plain, (k5_tmap_1(X1,esk1_1(X1))=u1_pre_topc(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_11])).
% 0.18/0.37  fof(c_0_21, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k6_tmap_1(esk2_0,esk3_0))&(v3_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.18/0.37  cnf(c_0_22, plain, (u1_pre_topc(k6_tmap_1(X1,esk1_1(X1)))=k5_tmap_1(X1,esk1_1(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_11])).
% 0.18/0.37  cnf(c_0_23, plain, (k6_tmap_1(X1,esk1_1(X1))=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_28, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=k5_tmap_1(X1,esk1_1(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.37  cnf(c_0_29, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k6_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk2_0,esk3_0))=k5_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (k5_tmap_1(esk2_0,esk1_1(esk2_0))=k5_tmap_1(esk2_0,esk3_0)|v3_pre_topc(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_25]), c_0_26])]), c_0_27])).
% 0.18/0.37  cnf(c_0_32, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_33, negated_conjecture, (k5_tmap_1(esk2_0,esk3_0)=u1_pre_topc(esk2_0)|v3_pre_topc(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_31]), c_0_25]), c_0_26])]), c_0_27])).
% 0.18/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,u1_pre_topc(esk2_0))|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_24]), c_0_26])])).
% 0.18/0.37  cnf(c_0_35, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_0,u1_pre_topc(esk2_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_24]), c_0_26])]), c_0_27]), c_0_34])).
% 0.18/0.37  cnf(c_0_37, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k6_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_38, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_24]), c_0_26])])).
% 0.18/0.37  cnf(c_0_39, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,esk3_0))=k6_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.18/0.37  cnf(c_0_40, negated_conjecture, (k5_tmap_1(esk2_0,esk3_0)=u1_pre_topc(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_36]), c_0_25]), c_0_24]), c_0_26])]), c_0_27])).
% 0.18/0.37  cnf(c_0_41, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k6_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.18/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_41]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 43
% 0.18/0.37  # Proof object clause steps            : 30
% 0.18/0.37  # Proof object formula steps           : 13
% 0.18/0.37  # Proof object conjectures             : 19
% 0.18/0.37  # Proof object clause conjectures      : 16
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 14
% 0.18/0.37  # Proof object initial formulas used   : 6
% 0.18/0.37  # Proof object generating inferences   : 14
% 0.18/0.37  # Proof object simplifying inferences  : 39
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 6
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 16
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 16
% 0.18/0.37  # Processed clauses                    : 35
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 1
% 0.18/0.37  # ...remaining for further processing  : 34
% 0.18/0.37  # Other redundant clauses eliminated   : 0
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 7
% 0.18/0.37  # Generated clauses                    : 63
% 0.18/0.37  # ...of the previous two non-trivial   : 60
% 0.18/0.37  # Contextual simplify-reflections      : 3
% 0.18/0.37  # Paramodulations                      : 63
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 0
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 27
% 0.18/0.37  #    Positive orientable unit clauses  : 7
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 2
% 0.18/0.37  #    Non-unit-clauses                  : 18
% 0.18/0.37  # Current number of unprocessed clauses: 41
% 0.18/0.37  # ...number of literals in the above   : 248
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 7
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 104
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 30
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.18/0.37  # Unit Clause-clause subsumption calls : 5
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 3
% 0.18/0.37  # BW rewrite match successes           : 3
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 3141
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.031 s
% 0.18/0.37  # System time              : 0.002 s
% 0.18/0.37  # Total time               : 0.033 s
% 0.18/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
