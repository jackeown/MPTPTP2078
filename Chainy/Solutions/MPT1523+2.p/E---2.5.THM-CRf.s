%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1523+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:06 EST 2020

% Result     : Theorem 20.52s
% Output     : CNFRefutation 20.52s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 375 expanded)
%              Number of clauses        :   36 ( 131 expanded)
%              Number of leaves         :    5 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 (3457 expanded)
%              Number of equality atoms :   30 ( 714 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_yellow_0,conjecture,(
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

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',dt_u1_orders_2)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',free_g1_orders_2)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',d10_orders_2)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',d9_orders_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t1_yellow_0])).

fof(c_0_6,plain,(
    ! [X6214] :
      ( ~ l1_orders_2(X6214)
      | m1_subset_1(u1_orders_2(X6214),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6214),u1_struct_0(X6214)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_7,negated_conjecture,
    ( l1_orders_2(esk1068_0)
    & l1_orders_2(esk1069_0)
    & g1_orders_2(u1_struct_0(esk1068_0),u1_orders_2(esk1068_0)) = g1_orders_2(u1_struct_0(esk1069_0),u1_orders_2(esk1069_0))
    & m1_subset_1(esk1070_0,u1_struct_0(esk1068_0))
    & m1_subset_1(esk1071_0,u1_struct_0(esk1068_0))
    & m1_subset_1(esk1072_0,u1_struct_0(esk1069_0))
    & m1_subset_1(esk1073_0,u1_struct_0(esk1069_0))
    & esk1070_0 = esk1072_0
    & esk1071_0 = esk1073_0
    & ( r2_orders_2(esk1068_0,esk1070_0,esk1071_0)
      | r1_orders_2(esk1068_0,esk1070_0,esk1071_0) )
    & ( ~ r2_orders_2(esk1069_0,esk1072_0,esk1073_0)
      | r1_orders_2(esk1068_0,esk1070_0,esk1071_0) )
    & ( r2_orders_2(esk1068_0,esk1070_0,esk1071_0)
      | ~ r1_orders_2(esk1069_0,esk1072_0,esk1073_0) )
    & ( ~ r2_orders_2(esk1069_0,esk1072_0,esk1073_0)
      | ~ r1_orders_2(esk1069_0,esk1072_0,esk1073_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X6275,X6276,X6277,X6278] :
      ( ( X6275 = X6277
        | g1_orders_2(X6275,X6276) != g1_orders_2(X6277,X6278)
        | ~ m1_subset_1(X6276,k1_zfmisc_1(k2_zfmisc_1(X6275,X6275))) )
      & ( X6276 = X6278
        | g1_orders_2(X6275,X6276) != g1_orders_2(X6277,X6278)
        | ~ m1_subset_1(X6276,k1_zfmisc_1(k2_zfmisc_1(X6275,X6275))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1069_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1068_0),u1_orders_2(esk1068_0)) = g1_orders_2(u1_struct_0(esk1069_0),u1_orders_2(esk1069_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1069_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1069_0),u1_struct_0(esk1069_0)))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,plain,(
    ! [X6099,X6100,X6101] :
      ( ( r1_orders_2(X6099,X6100,X6101)
        | ~ r2_orders_2(X6099,X6100,X6101)
        | ~ m1_subset_1(X6101,u1_struct_0(X6099))
        | ~ m1_subset_1(X6100,u1_struct_0(X6099))
        | ~ l1_orders_2(X6099) )
      & ( X6100 != X6101
        | ~ r2_orders_2(X6099,X6100,X6101)
        | ~ m1_subset_1(X6101,u1_struct_0(X6099))
        | ~ m1_subset_1(X6100,u1_struct_0(X6099))
        | ~ l1_orders_2(X6099) )
      & ( ~ r1_orders_2(X6099,X6100,X6101)
        | X6100 = X6101
        | r2_orders_2(X6099,X6100,X6101)
        | ~ m1_subset_1(X6101,u1_struct_0(X6099))
        | ~ m1_subset_1(X6100,u1_struct_0(X6099))
        | ~ l1_orders_2(X6099) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_15,negated_conjecture,
    ( r2_orders_2(esk1068_0,esk1070_0,esk1071_0)
    | r1_orders_2(esk1068_0,esk1070_0,esk1071_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( esk1070_0 = esk1072_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( esk1071_0 = esk1073_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk1071_0,u1_struct_0(esk1068_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk1070_0,u1_struct_0(esk1068_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_20,plain,(
    ! [X6167,X6168,X6169] :
      ( ( ~ r1_orders_2(X6167,X6168,X6169)
        | r2_hidden(k4_tarski(X6168,X6169),u1_orders_2(X6167))
        | ~ m1_subset_1(X6169,u1_struct_0(X6167))
        | ~ m1_subset_1(X6168,u1_struct_0(X6167))
        | ~ l1_orders_2(X6167) )
      & ( ~ r2_hidden(k4_tarski(X6168,X6169),u1_orders_2(X6167))
        | r1_orders_2(X6167,X6168,X6169)
        | ~ m1_subset_1(X6169,u1_struct_0(X6167))
        | ~ m1_subset_1(X6168,u1_struct_0(X6167))
        | ~ l1_orders_2(X6167) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_21,negated_conjecture,
    ( u1_orders_2(esk1069_0) = X1
    | g1_orders_2(u1_struct_0(esk1068_0),u1_orders_2(esk1068_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk1068_0,esk1072_0,esk1073_0)
    | r2_orders_2(esk1068_0,esk1072_0,esk1073_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_16]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk1068_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk1073_0,u1_struct_0(esk1068_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk1072_0,u1_struct_0(esk1068_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_27,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk1073_0,u1_struct_0(esk1069_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( u1_orders_2(esk1069_0) = u1_orders_2(esk1068_0) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk1068_0,esk1072_0,esk1073_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk1069_0,X1,esk1073_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1069_0))
    | ~ r2_hidden(k4_tarski(X1,esk1073_0),u1_orders_2(esk1068_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_10]),c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk1072_0,u1_struct_0(esk1069_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1072_0,esk1073_0),u1_orders_2(esk1068_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_35,negated_conjecture,
    ( r2_orders_2(esk1068_0,esk1070_0,esk1071_0)
    | ~ r1_orders_2(esk1069_0,esk1072_0,esk1073_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_orders_2(esk1069_0,esk1072_0,esk1073_0)
    | ~ r1_orders_2(esk1069_0,esk1072_0,esk1073_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk1069_0,esk1072_0,esk1073_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_38,negated_conjecture,
    ( r2_orders_2(esk1068_0,esk1072_0,esk1073_0)
    | ~ r1_orders_2(esk1069_0,esk1072_0,esk1073_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_16]),c_0_17])).

cnf(c_0_39,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_orders_2(esk1069_0,esk1072_0,esk1073_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_41,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( r2_orders_2(esk1068_0,esk1072_0,esk1073_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( esk1073_0 = esk1072_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_10]),c_0_28]),c_0_33])]),c_0_40])).

cnf(c_0_44,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_orders_2(esk1068_0,esk1072_0,esk1072_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_24]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
