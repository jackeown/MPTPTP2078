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
% DateTime   : Thu Dec  3 11:19:25 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 136 expanded)
%              Number of clauses        :   23 (  54 expanded)
%              Number of leaves         :    4 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 502 expanded)
%              Number of equality atoms :   22 ( 121 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v3_tdlat_3(X1) )
           => v3_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(d3_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_hidden(X2,u1_pre_topc(X1))
             => r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v3_tdlat_3(X1) )
             => v3_tdlat_3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_tex_2])).

fof(c_0_5,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | m1_subset_1(u1_pre_topc(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_6,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & l1_pre_topc(esk3_0)
    & g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))
    & v3_tdlat_3(esk2_0)
    & ~ v3_tdlat_3(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X6,X7,X8,X9] :
      ( ( X6 = X8
        | g1_pre_topc(X6,X7) != g1_pre_topc(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))) )
      & ( X7 = X9
        | g1_pre_topc(X6,X7) != g1_pre_topc(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( u1_pre_topc(esk3_0) = X1
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != g1_pre_topc(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ( ~ v3_tdlat_3(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ r2_hidden(X11,u1_pre_topc(X10))
        | r2_hidden(k6_subset_1(u1_struct_0(X10),X11),u1_pre_topc(X10))
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk1_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | v3_tdlat_3(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk1_1(X10),u1_pre_topc(X10))
        | v3_tdlat_3(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(k6_subset_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))
        | v3_tdlat_3(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).

cnf(c_0_17,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != g1_pre_topc(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_1(X1),u1_pre_topc(X1))
    | v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k6_subset_1(u1_struct_0(esk3_0),X1),u1_pre_topc(esk3_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_20]),c_0_21])]),c_0_22]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_9]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_24])).

cnf(c_0_29,plain,
    ( v3_tdlat_3(X1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),u1_pre_topc(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_9])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S031A
% 0.21/0.37  # and selection function PSelectStrongRRNonRROptimalLit.
% 0.21/0.37  #
% 0.21/0.37  # Preprocessing time       : 0.027 s
% 0.21/0.37  # Presaturation interreduction done
% 0.21/0.37  
% 0.21/0.37  # Proof found!
% 0.21/0.37  # SZS status Theorem
% 0.21/0.37  # SZS output start CNFRefutation
% 0.21/0.37  fof(t19_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tex_2)).
% 0.21/0.37  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.21/0.37  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.21/0.37  fof(d3_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))=>r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tdlat_3)).
% 0.21/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2))))), inference(assume_negation,[status(cth)],[t19_tex_2])).
% 0.21/0.37  fof(c_0_5, plain, ![X5]:(~l1_pre_topc(X5)|m1_subset_1(u1_pre_topc(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.21/0.37  fof(c_0_6, negated_conjecture, (l1_pre_topc(esk2_0)&(l1_pre_topc(esk3_0)&((g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))&v3_tdlat_3(esk2_0))&~v3_tdlat_3(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.21/0.37  fof(c_0_7, plain, ![X6, X7, X8, X9]:((X6=X8|g1_pre_topc(X6,X7)!=g1_pre_topc(X8,X9)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))))&(X7=X9|g1_pre_topc(X6,X7)!=g1_pre_topc(X8,X9)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.21/0.37  cnf(c_0_8, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.37  cnf(c_0_9, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_10, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.21/0.37  cnf(c_0_12, negated_conjecture, (u1_pre_topc(esk3_0)=X1|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=g1_pre_topc(X2,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.21/0.37  cnf(c_0_13, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_14, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.37  cnf(c_0_15, negated_conjecture, (u1_pre_topc(esk2_0)=u1_pre_topc(esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.37  fof(c_0_16, plain, ![X10, X11]:((~v3_tdlat_3(X10)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(~r2_hidden(X11,u1_pre_topc(X10))|r2_hidden(k6_subset_1(u1_struct_0(X10),X11),u1_pre_topc(X10))))|~l1_pre_topc(X10))&((m1_subset_1(esk1_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|v3_tdlat_3(X10)|~l1_pre_topc(X10))&((r2_hidden(esk1_1(X10),u1_pre_topc(X10))|v3_tdlat_3(X10)|~l1_pre_topc(X10))&(~r2_hidden(k6_subset_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))|v3_tdlat_3(X10)|~l1_pre_topc(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).
% 0.21/0.37  cnf(c_0_17, negated_conjecture, (u1_struct_0(esk3_0)=X1|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=g1_pre_topc(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_11])).
% 0.21/0.37  cnf(c_0_18, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(rw,[status(thm)],[c_0_13, c_0_15])).
% 0.21/0.37  cnf(c_0_19, plain, (r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.37  cnf(c_0_20, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_22, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.37  cnf(c_0_23, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.37  cnf(c_0_24, negated_conjecture, (~v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_25, plain, (r2_hidden(esk1_1(X1),u1_pre_topc(X1))|v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(k6_subset_1(u1_struct_0(esk3_0),X1),u1_pre_topc(esk3_0))|~r2_hidden(X1,u1_pre_topc(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_15]), c_0_20]), c_0_21])]), c_0_22]), c_0_22])).
% 0.21/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_9]), c_0_24])).
% 0.21/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_9]), c_0_24])).
% 0.21/0.37  cnf(c_0_29, plain, (v3_tdlat_3(X1)|~r2_hidden(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),u1_pre_topc(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.21/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_9])]), c_0_24]), ['proof']).
% 0.21/0.37  # SZS output end CNFRefutation
% 0.21/0.37  # Proof object total steps             : 32
% 0.21/0.37  # Proof object clause steps            : 23
% 0.21/0.37  # Proof object formula steps           : 9
% 0.21/0.37  # Proof object conjectures             : 19
% 0.21/0.37  # Proof object clause conjectures      : 16
% 0.21/0.37  # Proof object formula conjectures     : 3
% 0.21/0.37  # Proof object initial clauses used    : 12
% 0.21/0.37  # Proof object initial formulas used   : 4
% 0.21/0.37  # Proof object generating inferences   : 10
% 0.21/0.37  # Proof object simplifying inferences  : 13
% 0.21/0.37  # Training examples: 0 positive, 0 negative
% 0.21/0.37  # Parsed axioms                        : 4
% 0.21/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.37  # Initial clauses                      : 12
% 0.21/0.37  # Removed in clause preprocessing      : 0
% 0.21/0.37  # Initial clauses in saturation        : 12
% 0.21/0.37  # Processed clauses                    : 37
% 0.21/0.37  # ...of these trivial                  : 1
% 0.21/0.37  # ...subsumed                          : 1
% 0.21/0.37  # ...remaining for further processing  : 35
% 0.21/0.37  # Other redundant clauses eliminated   : 0
% 0.21/0.37  # Clauses deleted for lack of memory   : 0
% 0.21/0.37  # Backward-subsumed                    : 0
% 0.21/0.37  # Backward-rewritten                   : 3
% 0.21/0.37  # Generated clauses                    : 25
% 0.21/0.37  # ...of the previous two non-trivial   : 16
% 0.21/0.37  # Contextual simplify-reflections      : 0
% 0.21/0.37  # Paramodulations                      : 23
% 0.21/0.37  # Factorizations                       : 0
% 0.21/0.37  # Equation resolutions                 : 2
% 0.21/0.37  # Propositional unsat checks           : 0
% 0.21/0.37  #    Propositional check models        : 0
% 0.21/0.37  #    Propositional check unsatisfiable : 0
% 0.21/0.37  #    Propositional clauses             : 0
% 0.21/0.37  #    Propositional clauses after purity: 0
% 0.21/0.37  #    Propositional unsat core size     : 0
% 0.21/0.37  #    Propositional preprocessing time  : 0.000
% 0.21/0.37  #    Propositional encoding time       : 0.000
% 0.21/0.37  #    Propositional solver time         : 0.000
% 0.21/0.37  #    Success case prop preproc time    : 0.000
% 0.21/0.37  #    Success case prop encoding time   : 0.000
% 0.21/0.37  #    Success case prop solver time     : 0.000
% 0.21/0.37  # Current number of processed clauses  : 20
% 0.21/0.37  #    Positive orientable unit clauses  : 9
% 0.21/0.37  #    Positive unorientable unit clauses: 0
% 0.21/0.37  #    Negative unit clauses             : 1
% 0.21/0.37  #    Non-unit-clauses                  : 10
% 0.21/0.37  # Current number of unprocessed clauses: 1
% 0.21/0.37  # ...number of literals in the above   : 3
% 0.21/0.37  # Current number of archived formulas  : 0
% 0.21/0.37  # Current number of archived clauses   : 15
% 0.21/0.37  # Clause-clause subsumption calls (NU) : 10
% 0.21/0.37  # Rec. Clause-clause subsumption calls : 6
% 0.21/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.37  # Unit Clause-clause subsumption calls : 0
% 0.21/0.37  # Rewrite failures with RHS unbound    : 0
% 0.21/0.37  # BW rewrite match attempts            : 3
% 0.21/0.37  # BW rewrite match successes           : 2
% 0.21/0.37  # Condensation attempts                : 0
% 0.21/0.37  # Condensation successes               : 0
% 0.21/0.37  # Termbank termtop insertions          : 1322
% 0.21/0.37  
% 0.21/0.37  # -------------------------------------------------
% 0.21/0.37  # User time                : 0.028 s
% 0.21/0.37  # System time              : 0.004 s
% 0.21/0.37  # Total time               : 0.032 s
% 0.21/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
