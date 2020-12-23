%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:07 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  53 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    3 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :  207 ( 583 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d20_borsuk_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( r1_borsuk_1(X1,X2)
          <=> ? [X3] :
                ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v5_pre_topc(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                & v3_borsuk_1(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_borsuk_1)).

fof(t78_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v1_tdlat_3(X2)
            & m1_pre_topc(X2,X1) )
         => ? [X3] :
              ( v1_funct_1(X3)
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
              & v5_pre_topc(X3,X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
              & v3_borsuk_1(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tex_2)).

fof(t79_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v1_tdlat_3(X2)
            & m1_pre_topc(X2,X1) )
         => r1_borsuk_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tex_2)).

fof(c_0_3,plain,(
    ! [X4,X5,X7] :
      ( ( v1_funct_1(esk1_2(X4,X5))
        | ~ r1_borsuk_1(X4,X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( v1_funct_2(esk1_2(X4,X5),u1_struct_0(X4),u1_struct_0(X5))
        | ~ r1_borsuk_1(X4,X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( v5_pre_topc(esk1_2(X4,X5),X4,X5)
        | ~ r1_borsuk_1(X4,X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
        | ~ r1_borsuk_1(X4,X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( v3_borsuk_1(esk1_2(X4,X5),X4,X5)
        | ~ r1_borsuk_1(X4,X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X5))
        | ~ v5_pre_topc(X7,X4,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
        | ~ v3_borsuk_1(X7,X4,X5)
        | r1_borsuk_1(X4,X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_borsuk_1])])])])])])).

fof(c_0_4,plain,(
    ! [X8,X9] :
      ( ( v1_funct_1(esk2_2(X8,X9))
        | v2_struct_0(X9)
        | ~ v1_tdlat_3(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ v3_tdlat_3(X8)
        | ~ l1_pre_topc(X8) )
      & ( v1_funct_2(esk2_2(X8,X9),u1_struct_0(X8),u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v1_tdlat_3(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ v3_tdlat_3(X8)
        | ~ l1_pre_topc(X8) )
      & ( v5_pre_topc(esk2_2(X8,X9),X8,X9)
        | v2_struct_0(X9)
        | ~ v1_tdlat_3(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ v3_tdlat_3(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
        | v2_struct_0(X9)
        | ~ v1_tdlat_3(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ v3_tdlat_3(X8)
        | ~ l1_pre_topc(X8) )
      & ( v3_borsuk_1(esk2_2(X8,X9),X8,X9)
        | v2_struct_0(X9)
        | ~ v1_tdlat_3(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ v3_tdlat_3(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tex_2])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v1_tdlat_3(X2)
              & m1_pre_topc(X2,X1) )
           => r1_borsuk_1(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t79_tex_2])).

cnf(c_0_6,plain,
    ( r1_borsuk_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v3_borsuk_1(X1,X2,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v1_funct_1(esk2_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( v1_funct_2(esk2_2(X1,X2),u1_struct_0(X1),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( v5_pre_topc(esk2_2(X1,X2),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( v3_borsuk_1(esk2_2(X1,X2),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v3_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v1_tdlat_3(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ r1_borsuk_1(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_13,plain,
    ( r1_borsuk_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ v3_tdlat_3(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_borsuk_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_borsuk_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d20_borsuk_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(r1_borsuk_1(X1,X2)<=>?[X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&v3_borsuk_1(X3,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_borsuk_1)).
% 0.13/0.38  fof(t78_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v1_tdlat_3(X2))&m1_pre_topc(X2,X1))=>?[X3]:((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&v3_borsuk_1(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tex_2)).
% 0.13/0.38  fof(t79_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v1_tdlat_3(X2))&m1_pre_topc(X2,X1))=>r1_borsuk_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tex_2)).
% 0.13/0.38  fof(c_0_3, plain, ![X4, X5, X7]:((((((v1_funct_1(esk1_2(X4,X5))|~r1_borsuk_1(X4,X5)|(v2_struct_0(X5)|~m1_pre_topc(X5,X4))|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)))&(v1_funct_2(esk1_2(X4,X5),u1_struct_0(X4),u1_struct_0(X5))|~r1_borsuk_1(X4,X5)|(v2_struct_0(X5)|~m1_pre_topc(X5,X4))|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4))))&(v5_pre_topc(esk1_2(X4,X5),X4,X5)|~r1_borsuk_1(X4,X5)|(v2_struct_0(X5)|~m1_pre_topc(X5,X4))|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4))))&(m1_subset_1(esk1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))|~r1_borsuk_1(X4,X5)|(v2_struct_0(X5)|~m1_pre_topc(X5,X4))|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4))))&(v3_borsuk_1(esk1_2(X4,X5),X4,X5)|~r1_borsuk_1(X4,X5)|(v2_struct_0(X5)|~m1_pre_topc(X5,X4))|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4))))&(~v1_funct_1(X7)|~v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X5))|~v5_pre_topc(X7,X4,X5)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))|~v3_borsuk_1(X7,X4,X5)|r1_borsuk_1(X4,X5)|(v2_struct_0(X5)|~m1_pre_topc(X5,X4))|(v2_struct_0(X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_borsuk_1])])])])])])).
% 0.13/0.38  fof(c_0_4, plain, ![X8, X9]:(((((v1_funct_1(esk2_2(X8,X9))|(v2_struct_0(X9)|~v1_tdlat_3(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~v3_tdlat_3(X8)|~l1_pre_topc(X8)))&(v1_funct_2(esk2_2(X8,X9),u1_struct_0(X8),u1_struct_0(X9))|(v2_struct_0(X9)|~v1_tdlat_3(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~v3_tdlat_3(X8)|~l1_pre_topc(X8))))&(v5_pre_topc(esk2_2(X8,X9),X8,X9)|(v2_struct_0(X9)|~v1_tdlat_3(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~v3_tdlat_3(X8)|~l1_pre_topc(X8))))&(m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))|(v2_struct_0(X9)|~v1_tdlat_3(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~v3_tdlat_3(X8)|~l1_pre_topc(X8))))&(v3_borsuk_1(esk2_2(X8,X9),X8,X9)|(v2_struct_0(X9)|~v1_tdlat_3(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~v3_tdlat_3(X8)|~l1_pre_topc(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tex_2])])])])])])).
% 0.13/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v1_tdlat_3(X2))&m1_pre_topc(X2,X1))=>r1_borsuk_1(X1,X2)))), inference(assume_negation,[status(cth)],[t79_tex_2])).
% 0.13/0.38  cnf(c_0_6, plain, (r1_borsuk_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v3_borsuk_1(X1,X2,X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  cnf(c_0_7, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X2)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_8, plain, (v1_funct_1(esk2_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X2)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_9, plain, (v1_funct_2(esk2_2(X1,X2),u1_struct_0(X1),u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X2)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_10, plain, (v5_pre_topc(esk2_2(X1,X2),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X2)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_11, plain, (v3_borsuk_1(esk2_2(X1,X2),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X2)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v3_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v1_tdlat_3(esk4_0))&m1_pre_topc(esk4_0,esk3_0))&~r1_borsuk_1(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.13/0.38  cnf(c_0_13, plain, (r1_borsuk_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X2)|~v3_tdlat_3(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (v1_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (r1_borsuk_1(X1,esk4_0)|v2_struct_0(X1)|~v3_tdlat_3(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (~r1_borsuk_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 24
% 0.13/0.38  # Proof object clause steps            : 17
% 0.13/0.38  # Proof object formula steps           : 7
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 3
% 0.13/0.38  # Proof object generating inferences   : 3
% 0.13/0.38  # Proof object simplifying inferences  : 11
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 3
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 19
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 19
% 0.13/0.38  # Processed clauses                    : 21
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 21
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 4
% 0.13/0.38  # ...of the previous two non-trivial   : 2
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 4
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
% 0.13/0.38  # Current number of processed clauses  : 21
% 0.13/0.38  #    Positive orientable unit clauses  : 5
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 13
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 0
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 39
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 4
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1884
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.032 s
% 0.13/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
