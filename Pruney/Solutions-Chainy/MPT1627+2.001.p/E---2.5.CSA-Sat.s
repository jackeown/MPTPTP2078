%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:07 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   23 (  90 expanded)
%              Number of clauses        :   18 (  26 expanded)
%              Number of leaves         :    2 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :  123 ( 903 expanded)
%              Number of equality atoms :   13 ( 129 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & v4_waybel_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( ( v1_waybel_0(X3,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
             => ( r1_yellow_0(X1,X3)
               => ( X3 = k1_xboole_0
                  | ( r1_yellow_0(X2,X3)
                    & k1_yellow_0(X2,X3) = k1_yellow_0(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_0)).

fof(t65_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( ( r1_yellow_0(X1,X3)
                  & r2_hidden(k1_yellow_0(X1,X3),u1_struct_0(X2)) )
               => ( r1_yellow_0(X2,X3)
                  & k1_yellow_0(X2,X3) = k1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_yellow_0)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & v4_waybel_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( ( v1_waybel_0(X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
               => ( r1_yellow_0(X1,X3)
                 => ( X3 = k1_xboole_0
                    | ( r1_yellow_0(X2,X3)
                      & k1_yellow_0(X2,X3) = k1_yellow_0(X1,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_waybel_0])).

fof(c_0_3,plain,(
    ! [X4,X5,X6] :
      ( ( r1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X4,X6)
        | ~ r2_hidden(k1_yellow_0(X4,X6),u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v4_yellow_0(X5,X4)
        | ~ m1_yellow_0(X5,X4)
        | v2_struct_0(X4)
        | ~ v4_orders_2(X4)
        | ~ l1_orders_2(X4) )
      & ( k1_yellow_0(X5,X6) = k1_yellow_0(X4,X6)
        | ~ r1_yellow_0(X4,X6)
        | ~ r2_hidden(k1_yellow_0(X4,X6),u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v4_yellow_0(X5,X4)
        | ~ m1_yellow_0(X5,X4)
        | v2_struct_0(X4)
        | ~ v4_orders_2(X4)
        | ~ l1_orders_2(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_yellow_0])])])])])).

fof(c_0_4,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v4_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_yellow_0(esk2_0,esk1_0)
    & v4_waybel_0(esk2_0,esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & v1_waybel_0(esk3_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r1_yellow_0(esk1_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & ( ~ r1_yellow_0(esk2_0,esk3_0)
      | k1_yellow_0(esk2_0,esk3_0) != k1_yellow_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).

cnf(c_0_5,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_yellow_0(X3,X2)
    | ~ r2_hidden(k1_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,plain,
    ( r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_yellow_0(X3,X2)
    | ~ r2_hidden(k1_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ r2_hidden(k1_yellow_0(X1,esk3_0),u1_struct_0(esk2_0))
    | ~ r1_yellow_0(X1,esk3_0)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ v4_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( v4_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0)
    | v2_struct_0(X1)
    | ~ r2_hidden(k1_yellow_0(X1,esk3_0),u1_struct_0(esk2_0))
    | ~ r1_yellow_0(X1,esk3_0)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ v4_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_6]),c_0_7]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk1_0,esk3_0)
    | ~ r2_hidden(k1_yellow_0(esk1_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0)
    | ~ r2_hidden(k1_yellow_0(esk1_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_yellow_0(esk2_0,esk3_0)
    | k1_yellow_0(esk2_0,esk3_0) != k1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( v1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( v4_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.13/0.37  # and selection function PSelectMinOptimalNoXTypePred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # No proof found!
% 0.13/0.37  # SZS status CounterSatisfiable
% 0.13/0.37  # SZS output start Saturation
% 0.13/0.37  fof(t7_waybel_0, conjecture, ![X1]:(((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&v4_waybel_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3]:((v1_waybel_0(X3,X2)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r1_yellow_0(X1,X3)=>(X3=k1_xboole_0|(r1_yellow_0(X2,X3)&k1_yellow_0(X2,X3)=k1_yellow_0(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_waybel_0)).
% 0.13/0.37  fof(t65_yellow_0, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>((r1_yellow_0(X1,X3)&r2_hidden(k1_yellow_0(X1,X3),u1_struct_0(X2)))=>(r1_yellow_0(X2,X3)&k1_yellow_0(X2,X3)=k1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_yellow_0)).
% 0.13/0.37  fof(c_0_2, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&v4_waybel_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3]:((v1_waybel_0(X3,X2)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r1_yellow_0(X1,X3)=>(X3=k1_xboole_0|(r1_yellow_0(X2,X3)&k1_yellow_0(X2,X3)=k1_yellow_0(X1,X3)))))))), inference(assume_negation,[status(cth)],[t7_waybel_0])).
% 0.13/0.37  fof(c_0_3, plain, ![X4, X5, X6]:((r1_yellow_0(X5,X6)|(~r1_yellow_0(X4,X6)|~r2_hidden(k1_yellow_0(X4,X6),u1_struct_0(X5)))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v4_yellow_0(X5,X4)|~m1_yellow_0(X5,X4))|(v2_struct_0(X4)|~v4_orders_2(X4)|~l1_orders_2(X4)))&(k1_yellow_0(X5,X6)=k1_yellow_0(X4,X6)|(~r1_yellow_0(X4,X6)|~r2_hidden(k1_yellow_0(X4,X6),u1_struct_0(X5)))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v4_yellow_0(X5,X4)|~m1_yellow_0(X5,X4))|(v2_struct_0(X4)|~v4_orders_2(X4)|~l1_orders_2(X4)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_yellow_0])])])])])).
% 0.13/0.37  fof(c_0_4, negated_conjecture, (((~v2_struct_0(esk1_0)&v4_orders_2(esk1_0))&l1_orders_2(esk1_0))&((((~v2_struct_0(esk2_0)&v4_yellow_0(esk2_0,esk1_0))&v4_waybel_0(esk2_0,esk1_0))&m1_yellow_0(esk2_0,esk1_0))&((v1_waybel_0(esk3_0,esk2_0)&m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))))&(r1_yellow_0(esk1_0,esk3_0)&(esk3_0!=k1_xboole_0&(~r1_yellow_0(esk2_0,esk3_0)|k1_yellow_0(esk2_0,esk3_0)!=k1_yellow_0(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).
% 0.13/0.37  cnf(c_0_5, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X3,X2)|v2_struct_0(X1)|v2_struct_0(X3)|~r1_yellow_0(X3,X2)|~r2_hidden(k1_yellow_0(X3,X2),u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_yellow_0(X1,X3)|~m1_yellow_0(X1,X3)|~v4_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.13/0.37  cnf(c_0_6, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_7, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_8, plain, (r1_yellow_0(X1,X2)|v2_struct_0(X1)|v2_struct_0(X3)|~r1_yellow_0(X3,X2)|~r2_hidden(k1_yellow_0(X3,X2),u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_yellow_0(X1,X3)|~m1_yellow_0(X1,X3)|~v4_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (k1_yellow_0(esk2_0,esk3_0)=k1_yellow_0(X1,esk3_0)|v2_struct_0(X1)|~r2_hidden(k1_yellow_0(X1,esk3_0),u1_struct_0(esk2_0))|~r1_yellow_0(X1,esk3_0)|~m1_yellow_0(esk2_0,X1)|~v4_yellow_0(esk2_0,X1)|~l1_orders_2(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (r1_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (m1_yellow_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (v4_yellow_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (v4_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (r1_yellow_0(esk2_0,esk3_0)|v2_struct_0(X1)|~r2_hidden(k1_yellow_0(X1,esk3_0),u1_struct_0(esk2_0))|~r1_yellow_0(X1,esk3_0)|~m1_yellow_0(esk2_0,X1)|~v4_yellow_0(esk2_0,X1)|~l1_orders_2(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_6]), c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (k1_yellow_0(esk2_0,esk3_0)=k1_yellow_0(esk1_0,esk3_0)|~r2_hidden(k1_yellow_0(esk1_0,esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), ['final']).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (r1_yellow_0(esk2_0,esk3_0)|~r2_hidden(k1_yellow_0(esk1_0,esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), ['final']).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (~r1_yellow_0(esk2_0,esk3_0)|k1_yellow_0(esk2_0,esk3_0)!=k1_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (v1_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (v4_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  # SZS output end Saturation
% 0.13/0.37  # Proof object total steps             : 23
% 0.13/0.37  # Proof object clause steps            : 18
% 0.13/0.37  # Proof object formula steps           : 5
% 0.13/0.37  # Proof object conjectures             : 19
% 0.13/0.37  # Proof object clause conjectures      : 16
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 14
% 0.13/0.37  # Proof object initial formulas used   : 2
% 0.13/0.37  # Proof object generating inferences   : 4
% 0.13/0.37  # Proof object simplifying inferences  : 14
% 0.13/0.37  # Parsed axioms                        : 2
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 14
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 14
% 0.13/0.37  # Processed clauses                    : 32
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 32
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 6
% 0.13/0.37  # ...of the previous two non-trivial   : 4
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 4
% 0.13/0.37  # Factorizations                       : 2
% 0.13/0.37  # Equation resolutions                 : 0
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
% 0.13/0.37  # Current number of processed clauses  : 18
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 3
% 0.13/0.37  #    Non-unit-clauses                  : 7
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 14
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1238
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
