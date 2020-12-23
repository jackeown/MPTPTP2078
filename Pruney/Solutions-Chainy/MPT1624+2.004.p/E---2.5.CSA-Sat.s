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
% DateTime   : Thu Dec  3 11:16:06 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   24 (  54 expanded)
%              Number of clauses        :   17 (  19 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  122 ( 359 expanded)
%              Number of equality atoms :   25 (  83 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( X3 = X4
                        & v2_waybel_0(X3,X1) )
                     => v2_waybel_0(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( ( X3 = X5
                                & X4 = X6 )
                             => ( ( r1_orders_2(X1,X3,X4)
                                 => r1_orders_2(X2,X5,X6) )
                                & ( r2_orders_2(X1,X3,X4)
                                 => r2_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( ( X3 = X4
                          & v2_waybel_0(X3,X1) )
                       => v2_waybel_0(X4,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_waybel_0])).

fof(c_0_4,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & esk3_0 = esk4_0
    & v2_waybel_0(esk3_0,esk1_0)
    & ~ v2_waybel_0(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | m1_subset_1(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

fof(c_0_8,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r1_orders_2(X10,X12,X13)
        | r1_orders_2(X11,X14,X15)
        | X12 != X14
        | X13 != X15
        | ~ m1_subset_1(X15,u1_struct_0(X11))
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)) != g1_orders_2(u1_struct_0(X11),u1_orders_2(X11))
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) )
      & ( ~ r2_orders_2(X10,X12,X13)
        | r2_orders_2(X11,X14,X15)
        | X12 != X14
        | X13 != X15
        | ~ m1_subset_1(X15,u1_struct_0(X11))
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)) != g1_orders_2(u1_struct_0(X11),u1_orders_2(X11))
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_yellow_0])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_6,c_0_7]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_12,plain,
    ( r2_orders_2(X4,X5,X6)
    | ~ r2_orders_2(X1,X2,X3)
    | X2 != X5
    | X3 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_orders_2(X4,X5,X6)
    | ~ r1_orders_2(X1,X2,X3)
    | X2 != X5
    | X3 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_11]),
    [final]).

cnf(c_0_17,plain,
    ( r2_orders_2(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_orders_2(X4,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])]),
    [final]).

cnf(c_0_18,plain,
    ( r1_orders_2(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_orders_2(X4,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_waybel_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_7]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( v2_waybel_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.026 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # No proof found!
% 0.19/0.38  # SZS status CounterSatisfiable
% 0.19/0.38  # SZS output start Saturation
% 0.19/0.38  fof(t4_waybel_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((X3=X4&v2_waybel_0(X3,X1))=>v2_waybel_0(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_waybel_0)).
% 0.19/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.38  fof(t1_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>((X3=X5&X4=X6)=>((r1_orders_2(X1,X3,X4)=>r1_orders_2(X2,X5,X6))&(r2_orders_2(X1,X3,X4)=>r2_orders_2(X2,X5,X6))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_0)).
% 0.19/0.38  fof(c_0_3, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((X3=X4&v2_waybel_0(X3,X1))=>v2_waybel_0(X4,X2)))))))), inference(assume_negation,[status(cth)],[t4_waybel_0])).
% 0.19/0.38  fof(c_0_4, negated_conjecture, (l1_orders_2(esk1_0)&(l1_orders_2(esk2_0)&(g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((esk3_0=esk4_0&v2_waybel_0(esk3_0,esk1_0))&~v2_waybel_0(esk4_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.19/0.38  fof(c_0_5, plain, ![X7, X8, X9]:(~r2_hidden(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X9))|m1_subset_1(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.38  cnf(c_0_6, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.38  cnf(c_0_7, negated_conjecture, (esk3_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.19/0.38  fof(c_0_8, plain, ![X10, X11, X12, X13, X14, X15]:((~r1_orders_2(X10,X12,X13)|r1_orders_2(X11,X14,X15)|(X12!=X14|X13!=X15)|~m1_subset_1(X15,u1_struct_0(X11))|~m1_subset_1(X14,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|g1_orders_2(u1_struct_0(X10),u1_orders_2(X10))!=g1_orders_2(u1_struct_0(X11),u1_orders_2(X11))|~l1_orders_2(X11)|~l1_orders_2(X10))&(~r2_orders_2(X10,X12,X13)|r2_orders_2(X11,X14,X15)|(X12!=X14|X13!=X15)|~m1_subset_1(X15,u1_struct_0(X11))|~m1_subset_1(X14,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|g1_orders_2(u1_struct_0(X10),u1_orders_2(X10))!=g1_orders_2(u1_struct_0(X11),u1_orders_2(X11))|~l1_orders_2(X11)|~l1_orders_2(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_yellow_0])])])])).
% 0.19/0.38  cnf(c_0_9, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_6, c_0_7]), ['final']).
% 0.19/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.19/0.38  cnf(c_0_12, plain, (r2_orders_2(X4,X5,X6)|~r2_orders_2(X1,X2,X3)|X2!=X5|X3!=X6|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))|~l1_orders_2(X4)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_13, plain, (r1_orders_2(X4,X5,X6)|~r1_orders_2(X1,X2,X3)|X2!=X5|X3!=X6|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))|~l1_orders_2(X4)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (~v2_waybel_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk1_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_9, c_0_11]), ['final']).
% 0.19/0.38  cnf(c_0_17, plain, (r2_orders_2(X1,X2,X3)|g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))!=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~r2_orders_2(X4,X2,X3)|~l1_orders_2(X1)|~l1_orders_2(X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X4))|~m1_subset_1(X2,u1_struct_0(X4))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])]), ['final']).
% 0.19/0.38  cnf(c_0_18, plain, (r1_orders_2(X1,X2,X3)|g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))!=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~r1_orders_2(X4,X2,X3)|~l1_orders_2(X1)|~l1_orders_2(X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X4))|~m1_subset_1(X2,u1_struct_0(X4))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])]), ['final']).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (~v2_waybel_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_14, c_0_7]), ['final']).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (v2_waybel_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.19/0.38  # SZS output end Saturation
% 0.19/0.38  # Proof object total steps             : 24
% 0.19/0.38  # Proof object clause steps            : 17
% 0.19/0.38  # Proof object formula steps           : 7
% 0.19/0.38  # Proof object conjectures             : 15
% 0.19/0.38  # Proof object clause conjectures      : 12
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 11
% 0.19/0.38  # Proof object initial formulas used   : 3
% 0.19/0.38  # Proof object generating inferences   : 2
% 0.19/0.38  # Proof object simplifying inferences  : 6
% 0.19/0.38  # Parsed axioms                        : 3
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 11
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 11
% 0.19/0.38  # Processed clauses                    : 26
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 26
% 0.19/0.38  # Other redundant clauses eliminated   : 4
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 4
% 0.19/0.38  # ...of the previous two non-trivial   : 4
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 2
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 4
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 13
% 0.19/0.38  #    Positive orientable unit clauses  : 7
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 5
% 0.19/0.38  # Current number of unprocessed clauses: 0
% 0.19/0.38  # ...number of literals in the above   : 0
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 11
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 31
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 0
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 2
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 1201
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.027 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.031 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
