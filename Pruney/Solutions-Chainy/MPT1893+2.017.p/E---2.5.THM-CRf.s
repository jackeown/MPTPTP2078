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
% DateTime   : Thu Dec  3 11:20:52 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 254 expanded)
%              Number of clauses        :   26 (  80 expanded)
%              Number of leaves         :    9 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 (1679 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( ( v3_pre_topc(X2,X1)
                | v4_pre_topc(X2,X1) )
              & v3_tex_2(X2,X1)
              & v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

fof(t23_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

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

fof(fc12_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( ( v3_pre_topc(X2,X1)
                  | v4_pre_topc(X2,X1) )
                & v3_tex_2(X2,X1)
                & v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_tex_2])).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ( ~ v3_tdlat_3(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v3_pre_topc(X11,X10)
        | v4_pre_topc(X11,X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk1_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | v3_tdlat_3(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v3_pre_topc(esk1_1(X10),X10)
        | v3_tdlat_3(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ v4_pre_topc(esk1_1(X10),X10)
        | v3_tdlat_3(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_tdlat_3])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v3_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( v3_pre_topc(esk4_0,esk3_0)
      | v4_pre_topc(esk4_0,esk3_0) )
    & v3_tex_2(esk4_0,esk3_0)
    & v1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ( ~ v3_tdlat_3(X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v4_pre_topc(X14,X13)
        | v3_pre_topc(X14,X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | v3_tdlat_3(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v4_pre_topc(esk2_1(X13),X13)
        | v3_tdlat_3(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ v3_pre_topc(esk2_1(X13),X13)
        | v3_tdlat_3(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_13,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X6,X7] :
      ( ( ~ v4_pre_topc(X7,X6)
        | k2_pre_topc(X6,X7) = X7
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( ~ v2_pre_topc(X6)
        | k2_pre_topc(X6,X7) != X7
        | v4_pre_topc(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ v3_pre_topc(X17,X16)
      | ~ v3_tex_2(X17,X16)
      | v1_tops_1(X17,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).

cnf(c_0_21,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

fof(c_0_23,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | ~ v1_subset_1(k2_struct_0(X5),u1_struct_0(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).

fof(c_0_24,plain,(
    ! [X3] :
      ( ~ l1_struct_0(X3)
      | k2_struct_0(X3) = u1_struct_0(X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ( ~ v1_tops_1(X9,X8)
        | k2_pre_topc(X8,X9) = u1_struct_0(X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( k2_pre_topc(X8,X9) != u1_struct_0(X8)
        | v1_tops_1(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

cnf(c_0_26,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_22])])).

cnf(c_0_31,plain,
    ( ~ l1_struct_0(X1)
    | ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k2_pre_topc(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_17])]),c_0_22])])).

cnf(c_0_35,negated_conjecture,
    ( v1_tops_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_14]),c_0_28]),c_0_16]),c_0_17])]),c_0_29]),c_0_30])])).

cnf(c_0_36,plain,
    ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_14]),c_0_17])]),c_0_34]),c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_subset_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( v1_subset_1(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

fof(c_0_41,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | l1_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_42,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_43,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:39:20 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.36  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.17/0.36  # and selection function SelectNewComplexAHP.
% 0.17/0.36  #
% 0.17/0.36  # Preprocessing time       : 0.029 s
% 0.17/0.36  # Presaturation interreduction done
% 0.17/0.36  
% 0.17/0.36  # Proof found!
% 0.17/0.36  # SZS status Theorem
% 0.17/0.36  # SZS output start CNFRefutation
% 0.17/0.36  fof(t61_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 0.17/0.36  fof(t23_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tdlat_3)).
% 0.17/0.36  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.17/0.36  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.17/0.36  fof(t47_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tex_2(X2,X1))=>v1_tops_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 0.17/0.36  fof(fc12_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>~(v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 0.17/0.36  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.17/0.36  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 0.17/0.36  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.17/0.36  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t61_tex_2])).
% 0.17/0.36  fof(c_0_10, plain, ![X10, X11]:((~v3_tdlat_3(X10)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(~v3_pre_topc(X11,X10)|v4_pre_topc(X11,X10)))|(~v2_pre_topc(X10)|~l1_pre_topc(X10)))&((m1_subset_1(esk1_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|v3_tdlat_3(X10)|(~v2_pre_topc(X10)|~l1_pre_topc(X10)))&((v3_pre_topc(esk1_1(X10),X10)|v3_tdlat_3(X10)|(~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~v4_pre_topc(esk1_1(X10),X10)|v3_tdlat_3(X10)|(~v2_pre_topc(X10)|~l1_pre_topc(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_tdlat_3])])])])])).
% 0.17/0.36  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v3_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((v3_pre_topc(esk4_0,esk3_0)|v4_pre_topc(esk4_0,esk3_0))&v3_tex_2(esk4_0,esk3_0))&v1_subset_1(esk4_0,u1_struct_0(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.17/0.36  fof(c_0_12, plain, ![X13, X14]:((~v3_tdlat_3(X13)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(~v4_pre_topc(X14,X13)|v3_pre_topc(X14,X13)))|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))&((m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|v3_tdlat_3(X13)|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))&((v4_pre_topc(esk2_1(X13),X13)|v3_tdlat_3(X13)|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~v3_pre_topc(esk2_1(X13),X13)|v3_tdlat_3(X13)|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.17/0.36  cnf(c_0_13, plain, (v4_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.36  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.36  cnf(c_0_15, negated_conjecture, (v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.36  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.36  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.36  cnf(c_0_18, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|v4_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.36  fof(c_0_19, plain, ![X6, X7]:((~v4_pre_topc(X7,X6)|k2_pre_topc(X6,X7)=X7|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~l1_pre_topc(X6))&(~v2_pre_topc(X6)|k2_pre_topc(X6,X7)!=X7|v4_pre_topc(X7,X6)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~l1_pre_topc(X6))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.17/0.36  fof(c_0_20, plain, ![X16, X17]:(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(~v3_pre_topc(X17,X16)|~v3_tex_2(X17,X16)|v1_tops_1(X17,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).
% 0.17/0.36  cnf(c_0_21, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.36  cnf(c_0_22, negated_conjecture, (v4_pre_topc(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.17/0.36  fof(c_0_23, plain, ![X5]:(~l1_struct_0(X5)|~v1_subset_1(k2_struct_0(X5),u1_struct_0(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).
% 0.17/0.36  fof(c_0_24, plain, ![X3]:(~l1_struct_0(X3)|k2_struct_0(X3)=u1_struct_0(X3)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.17/0.36  fof(c_0_25, plain, ![X8, X9]:((~v1_tops_1(X9,X8)|k2_pre_topc(X8,X9)=u1_struct_0(X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(k2_pre_topc(X8,X9)!=u1_struct_0(X8)|v1_tops_1(X9,X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.17/0.36  cnf(c_0_26, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.36  cnf(c_0_27, plain, (v2_struct_0(X1)|v1_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.36  cnf(c_0_28, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.36  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.36  cnf(c_0_30, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_22])])).
% 0.17/0.36  cnf(c_0_31, plain, (~l1_struct_0(X1)|~v1_subset_1(k2_struct_0(X1),u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.36  cnf(c_0_32, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.36  cnf(c_0_33, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.36  cnf(c_0_34, negated_conjecture, (k2_pre_topc(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_14]), c_0_17])]), c_0_22])])).
% 0.17/0.36  cnf(c_0_35, negated_conjecture, (v1_tops_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_14]), c_0_28]), c_0_16]), c_0_17])]), c_0_29]), c_0_30])])).
% 0.17/0.36  cnf(c_0_36, plain, (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X1))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.17/0.36  cnf(c_0_37, negated_conjecture, (u1_struct_0(esk3_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_14]), c_0_17])]), c_0_34]), c_0_35])])).
% 0.17/0.36  cnf(c_0_38, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.36  cnf(c_0_39, negated_conjecture, (~v1_subset_1(esk4_0,esk4_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.17/0.36  cnf(c_0_40, negated_conjecture, (v1_subset_1(esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_38, c_0_37])).
% 0.17/0.36  fof(c_0_41, plain, ![X4]:(~l1_pre_topc(X4)|l1_struct_0(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.17/0.36  cnf(c_0_42, negated_conjecture, (~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.17/0.36  cnf(c_0_43, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.17/0.36  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_17])]), ['proof']).
% 0.17/0.36  # SZS output end CNFRefutation
% 0.17/0.36  # Proof object total steps             : 45
% 0.17/0.36  # Proof object clause steps            : 26
% 0.17/0.36  # Proof object formula steps           : 19
% 0.17/0.36  # Proof object conjectures             : 20
% 0.17/0.36  # Proof object clause conjectures      : 17
% 0.17/0.36  # Proof object formula conjectures     : 3
% 0.17/0.36  # Proof object initial clauses used    : 16
% 0.17/0.36  # Proof object initial formulas used   : 9
% 0.17/0.36  # Proof object generating inferences   : 8
% 0.17/0.36  # Proof object simplifying inferences  : 32
% 0.17/0.36  # Training examples: 0 positive, 0 negative
% 0.17/0.36  # Parsed axioms                        : 9
% 0.17/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.36  # Initial clauses                      : 24
% 0.17/0.36  # Removed in clause preprocessing      : 0
% 0.17/0.36  # Initial clauses in saturation        : 24
% 0.17/0.36  # Processed clauses                    : 58
% 0.17/0.36  # ...of these trivial                  : 0
% 0.17/0.36  # ...subsumed                          : 0
% 0.17/0.36  # ...remaining for further processing  : 58
% 0.17/0.36  # Other redundant clauses eliminated   : 0
% 0.17/0.36  # Clauses deleted for lack of memory   : 0
% 0.17/0.36  # Backward-subsumed                    : 0
% 0.17/0.36  # Backward-rewritten                   : 4
% 0.17/0.36  # Generated clauses                    : 29
% 0.17/0.36  # ...of the previous two non-trivial   : 23
% 0.17/0.36  # Contextual simplify-reflections      : 1
% 0.17/0.36  # Paramodulations                      : 29
% 0.17/0.36  # Factorizations                       : 0
% 0.17/0.36  # Equation resolutions                 : 0
% 0.17/0.36  # Propositional unsat checks           : 0
% 0.17/0.36  #    Propositional check models        : 0
% 0.17/0.36  #    Propositional check unsatisfiable : 0
% 0.17/0.36  #    Propositional clauses             : 0
% 0.17/0.36  #    Propositional clauses after purity: 0
% 0.17/0.36  #    Propositional unsat core size     : 0
% 0.17/0.36  #    Propositional preprocessing time  : 0.000
% 0.17/0.36  #    Propositional encoding time       : 0.000
% 0.17/0.36  #    Propositional solver time         : 0.000
% 0.17/0.36  #    Success case prop preproc time    : 0.000
% 0.17/0.36  #    Success case prop encoding time   : 0.000
% 0.17/0.36  #    Success case prop solver time     : 0.000
% 0.17/0.36  # Current number of processed clauses  : 30
% 0.17/0.36  #    Positive orientable unit clauses  : 11
% 0.17/0.36  #    Positive unorientable unit clauses: 0
% 0.17/0.36  #    Negative unit clauses             : 2
% 0.17/0.36  #    Non-unit-clauses                  : 17
% 0.17/0.36  # Current number of unprocessed clauses: 12
% 0.17/0.36  # ...number of literals in the above   : 52
% 0.17/0.36  # Current number of archived formulas  : 0
% 0.17/0.36  # Current number of archived clauses   : 28
% 0.17/0.36  # Clause-clause subsumption calls (NU) : 80
% 0.17/0.36  # Rec. Clause-clause subsumption calls : 6
% 0.17/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.17/0.36  # Unit Clause-clause subsumption calls : 0
% 0.17/0.36  # Rewrite failures with RHS unbound    : 0
% 0.17/0.36  # BW rewrite match attempts            : 3
% 0.17/0.36  # BW rewrite match successes           : 3
% 0.17/0.36  # Condensation attempts                : 0
% 0.17/0.36  # Condensation successes               : 0
% 0.17/0.36  # Termbank termtop insertions          : 2622
% 0.17/0.36  
% 0.17/0.36  # -------------------------------------------------
% 0.17/0.36  # User time                : 0.029 s
% 0.17/0.36  # System time              : 0.006 s
% 0.17/0.36  # Total time               : 0.035 s
% 0.17/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
