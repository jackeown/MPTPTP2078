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
% DateTime   : Thu Dec  3 11:21:33 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   42 (  75 expanded)
%              Number of clauses        :   23 (  27 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  194 ( 386 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t189_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

fof(d8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(d1_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ( v2_struct_0(X1)
      <=> v1_xboole_0(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).

fof(d11_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ? [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( r1_orders_2(X2,X4,X5)
                       => r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(t8_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_9,plain,(
    ! [X8,X9,X10,X11] :
      ( v1_xboole_0(X8)
      | v1_xboole_0(X9)
      | ~ m1_subset_1(X10,X8)
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,X8,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | r2_hidden(k3_funct_2(X8,X9,X11,X10),k2_relset_1(X8,X9,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).

fof(c_0_10,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ l1_struct_0(X21)
      | v2_struct_0(X22)
      | ~ l1_waybel_0(X22,X21)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | k2_waybel_0(X21,X22,X23) = k3_funct_2(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22),X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).

fof(c_0_11,plain,(
    ! [X26,X27] :
      ( ( v1_funct_1(u1_waybel_0(X26,X27))
        | ~ l1_struct_0(X26)
        | ~ l1_waybel_0(X27,X26) )
      & ( v1_funct_2(u1_waybel_0(X26,X27),u1_struct_0(X27),u1_struct_0(X26))
        | ~ l1_struct_0(X26)
        | ~ l1_waybel_0(X27,X26) )
      & ( m1_subset_1(u1_waybel_0(X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
        | ~ l1_struct_0(X26)
        | ~ l1_waybel_0(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

fof(c_0_12,plain,(
    ! [X28] :
      ( ( ~ v2_struct_0(X28)
        | v1_xboole_0(u1_struct_0(X28))
        | ~ l1_struct_0(X28) )
      & ( ~ v1_xboole_0(u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ l1_struct_0(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_struct_0])])])).

fof(c_0_13,plain,(
    ! [X13,X14,X15,X17,X18,X19] :
      ( ( m1_subset_1(esk2_3(X13,X14,X15),u1_struct_0(X14))
        | ~ r1_waybel_0(X13,X14,X15)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r1_orders_2(X14,esk2_3(X13,X14,X15),X17)
        | r2_hidden(k2_waybel_0(X13,X14,X17),X15)
        | ~ r1_waybel_0(X13,X14,X15)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( m1_subset_1(esk3_4(X13,X14,X18,X19),u1_struct_0(X14))
        | ~ m1_subset_1(X19,u1_struct_0(X14))
        | r1_waybel_0(X13,X14,X18)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( r1_orders_2(X14,X19,esk3_4(X13,X14,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X14))
        | r1_waybel_0(X13,X14,X18)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( ~ r2_hidden(k2_waybel_0(X13,X14,esk3_4(X13,X14,X18,X19)),X18)
        | ~ m1_subset_1(X19,u1_struct_0(X14))
        | r1_waybel_0(X13,X14,X18)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))
    | ~ m1_subset_1(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_funct_1(u1_waybel_0(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_9])).

cnf(c_0_21,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(k2_waybel_0(X1,X2,X3),k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_24,plain,(
    ! [X6] : m1_subset_1(esk1_1(X6),X6) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_25,plain,(
    ! [X24,X25] :
      ( ~ l1_struct_0(X24)
      | ~ l1_waybel_0(X25,X24)
      | l1_orders_2(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_struct_0(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & l1_waybel_0(esk5_0,esk4_0)
    & ~ r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_27,plain,
    ( r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_30,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_31]),c_0_32])]),c_0_35]),c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_39]),c_0_40])]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C00_02_nc_F1_SE_CS_SP_PS_S033N
% 0.13/0.38  # and selection function PSelectUnlessUniqMax.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.030 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t189_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 0.13/0.38  fof(d8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_waybel_0)).
% 0.13/0.38  fof(dt_u1_waybel_0, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 0.13/0.38  fof(d1_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>(v2_struct_0(X1)<=>v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_struct_0)).
% 0.13/0.38  fof(d11_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r2_hidden(k2_waybel_0(X1,X2,X5),X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 0.13/0.38  fof(t8_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 0.13/0.38  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.13/0.38  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.13/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.38  fof(c_0_9, plain, ![X8, X9, X10, X11]:(v1_xboole_0(X8)|(v1_xboole_0(X9)|(~m1_subset_1(X10,X8)|(~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|r2_hidden(k3_funct_2(X8,X9,X11,X10),k2_relset_1(X8,X9,X11)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).
% 0.13/0.38  fof(c_0_10, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~l1_struct_0(X21)|(v2_struct_0(X22)|~l1_waybel_0(X22,X21)|(~m1_subset_1(X23,u1_struct_0(X22))|k2_waybel_0(X21,X22,X23)=k3_funct_2(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22),X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X26, X27]:(((v1_funct_1(u1_waybel_0(X26,X27))|(~l1_struct_0(X26)|~l1_waybel_0(X27,X26)))&(v1_funct_2(u1_waybel_0(X26,X27),u1_struct_0(X27),u1_struct_0(X26))|(~l1_struct_0(X26)|~l1_waybel_0(X27,X26))))&(m1_subset_1(u1_waybel_0(X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))|(~l1_struct_0(X26)|~l1_waybel_0(X27,X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X28]:((~v2_struct_0(X28)|v1_xboole_0(u1_struct_0(X28))|~l1_struct_0(X28))&(~v1_xboole_0(u1_struct_0(X28))|v2_struct_0(X28)|~l1_struct_0(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_struct_0])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X13, X14, X15, X17, X18, X19]:(((m1_subset_1(esk2_3(X13,X14,X15),u1_struct_0(X14))|~r1_waybel_0(X13,X14,X15)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13)))&(~m1_subset_1(X17,u1_struct_0(X14))|(~r1_orders_2(X14,esk2_3(X13,X14,X15),X17)|r2_hidden(k2_waybel_0(X13,X14,X17),X15))|~r1_waybel_0(X13,X14,X15)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13))))&((m1_subset_1(esk3_4(X13,X14,X18,X19),u1_struct_0(X14))|~m1_subset_1(X19,u1_struct_0(X14))|r1_waybel_0(X13,X14,X18)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13)))&((r1_orders_2(X14,X19,esk3_4(X13,X14,X18,X19))|~m1_subset_1(X19,u1_struct_0(X14))|r1_waybel_0(X13,X14,X18)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13)))&(~r2_hidden(k2_waybel_0(X13,X14,esk3_4(X13,X14,X18,X19)),X18)|~m1_subset_1(X19,u1_struct_0(X14))|r1_waybel_0(X13,X14,X18)|(v2_struct_0(X14)|~l1_waybel_0(X14,X13))|(v2_struct_0(X13)|~l1_struct_0(X13)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).
% 0.13/0.38  cnf(c_0_14, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))|~m1_subset_1(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_15, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_16, plain, (m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_17, plain, (v1_funct_1(u1_waybel_0(X1,X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_19, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_9])).
% 0.13/0.38  cnf(c_0_21, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_22, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k2_waybel_0(X1,X2,X3),k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])).
% 0.13/0.38  cnf(c_0_23, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_24, plain, ![X6]:m1_subset_1(esk1_1(X6),X6), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.13/0.38  fof(c_0_25, plain, ![X24, X25]:(~l1_struct_0(X24)|(~l1_waybel_0(X25,X24)|l1_orders_2(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.13/0.38  fof(c_0_26, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_struct_0(esk4_0))&((~v2_struct_0(esk5_0)&l1_waybel_0(esk5_0,esk4_0))&~r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.13/0.38  cnf(c_0_27, plain, (r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|v2_struct_0(X1)|v2_struct_0(X2)|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_28, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  fof(c_0_29, plain, ![X12]:(~l1_orders_2(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.38  cnf(c_0_30, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (l1_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (l1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (~r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_34, plain, (r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|v2_struct_0(X2)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_37, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (l1_orders_2(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_31]), c_0_32])]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_39]), c_0_40])]), c_0_35]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 42
% 0.13/0.38  # Proof object clause steps            : 23
% 0.13/0.38  # Proof object formula steps           : 19
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 16
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 7
% 0.13/0.38  # Proof object simplifying inferences  : 15
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 9
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 20
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 20
% 0.13/0.38  # Processed clauses                    : 47
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 47
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 12
% 0.13/0.38  # ...of the previous two non-trivial   : 9
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 12
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 26
% 0.13/0.38  #    Positive orientable unit clauses  : 6
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 17
% 0.13/0.38  # Current number of unprocessed clauses: 2
% 0.13/0.38  # ...number of literals in the above   : 21
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 21
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 539
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 62
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.13/0.38  # Unit Clause-clause subsumption calls : 22
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2599
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
