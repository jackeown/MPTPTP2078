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
% DateTime   : Thu Dec  3 11:20:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 (4172 expanded)
%              Number of clauses        :   67 (1716 expanded)
%              Number of leaves         :    6 ( 973 expanded)
%              Depth                    :   19
%              Number of atoms          :  323 (21509 expanded)
%              Number of equality atoms :   43 (5919 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & X3 = X4
                      & v3_tex_2(X3,X1) )
                   => v3_tex_2(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tex_2)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d5_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                        & X3 = X4
                        & v3_tex_2(X3,X1) )
                     => v3_tex_2(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_tex_2])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X8 = X10
        | g1_pre_topc(X8,X9) != g1_pre_topc(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) )
      & ( X9 = X11
        | g1_pre_topc(X8,X9) != g1_pre_topc(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    & esk6_0 = esk7_0
    & v3_tex_2(esk6_0,esk4_0)
    & ~ v3_tex_2(esk7_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( X1 = u1_pre_topc(esk5_0)
    | g1_pre_topc(X2,X1) != g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_12,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | m1_subset_1(u1_pre_topc(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_13,negated_conjecture,
    ( u1_pre_topc(esk5_0) = u1_pre_topc(esk4_0)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( u1_pre_topc(esk5_0) = u1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_16]),c_0_17])])).

fof(c_0_21,plain,(
    ! [X12,X13,X14,X17] :
      ( ( m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r1_tarski(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(esk1_3(X12,X13,X14),X12)
        | ~ r1_tarski(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( k9_subset_1(u1_struct_0(X12),X13,esk1_3(X12,X13,X14)) = X14
        | ~ r1_tarski(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r1_tarski(esk2_2(X12,X13),X13)
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v3_pre_topc(X17,X12)
        | k9_subset_1(u1_struct_0(X12),X13,X17) != esk2_2(X12,X13)
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != g1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

fof(c_0_23,plain,(
    ! [X5,X6] :
      ( ( ~ v3_pre_topc(X6,X5)
        | r2_hidden(X6,u1_pre_topc(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(X6,u1_pre_topc(X5))
        | v3_pre_topc(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_24,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk2_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(esk5_0) = u1_struct_0(esk4_0) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v2_tex_2(X1,esk5_0)
    | k9_subset_1(u1_struct_0(esk4_0),X1,X2) != esk2_2(esk5_0,X1)
    | ~ v3_pre_topc(X2,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_17])])).

cnf(c_0_30,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v2_tex_2(X1,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_25]),c_0_17])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk2_2(esk5_0,X1),X1)
    | v2_tex_2(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_17])])).

cnf(c_0_33,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_17])]),c_0_25])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X18,X19,X20] :
      ( ( v2_tex_2(X19,X18)
        | ~ v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X20,X18)
        | ~ r1_tarski(X19,X20)
        | X19 = X20
        | ~ v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk3_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X19,X18)
        | v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( v2_tex_2(esk3_2(X18,X19),X18)
        | ~ v2_tex_2(X19,X18)
        | v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( r1_tarski(X19,esk3_2(X18,X19))
        | ~ v2_tex_2(X19,X18)
        | v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( X19 != esk3_2(X18,X19)
        | ~ v2_tex_2(X19,X18)
        | v3_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( ~ v3_tex_2(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( v2_tex_2(X1,esk5_0)
    | ~ v2_tex_2(X1,esk4_0)
    | ~ v3_pre_topc(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),esk5_0)
    | ~ m1_subset_1(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15])])]),c_0_31]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_15])])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( ~ v3_tex_2(esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v2_tex_2(X1,esk5_0)
    | ~ v2_tex_2(X1,esk4_0)
    | ~ v3_pre_topc(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),esk4_0)
    | ~ m1_subset_1(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_17])]),c_0_25])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk3_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_17])]),c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v2_tex_2(X1,esk5_0)
    | ~ v2_tex_2(X1,esk4_0)
    | ~ m1_subset_1(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_15])]),c_0_31]),c_0_32])).

cnf(c_0_50,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( v3_tex_2(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_53,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,esk3_2(X2,X1))
    | v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_46]),c_0_15])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk1_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X2,X1)
    | ~ v2_tex_2(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_17])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk3_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( v2_tex_2(X1,esk5_0)
    | ~ v2_tex_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_15])]),c_0_31]),c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( v2_tex_2(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_15])]),c_0_52])])).

cnf(c_0_60,plain,
    ( v2_tex_2(esk3_2(X1,X2),X1)
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( X1 = esk6_0
    | ~ r1_tarski(esk6_0,X1)
    | ~ v2_tex_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_51]),c_0_15])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_2(esk5_0,esk6_0))
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_42]),c_0_17])]),c_0_43])).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),X1,esk1_3(esk5_0,X1,X2)) = X2
    | ~ r1_tarski(X2,X1)
    | ~ v2_tex_2(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_17])])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk5_0,X1,X2),esk4_0)
    | ~ r1_tarski(X2,X1)
    | ~ v2_tex_2(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_45]),c_0_25]),c_0_25]),c_0_17])]),c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk2_2(esk4_0,esk3_2(esk5_0,esk6_0)),esk3_2(esk5_0,esk6_0))
    | v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_57]),c_0_15])])).

cnf(c_0_66,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_52]),c_0_59])])).

cnf(c_0_67,negated_conjecture,
    ( v2_tex_2(esk3_2(esk5_0,esk6_0),esk5_0)
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_42]),c_0_17])]),c_0_43])).

cnf(c_0_68,negated_conjecture,
    ( v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)
    | m1_subset_1(esk2_2(esk4_0,esk3_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_57]),c_0_15])])).

cnf(c_0_69,negated_conjecture,
    ( esk3_2(esk5_0,esk6_0) = esk6_0
    | ~ v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( v2_tex_2(X1,esk4_0)
    | ~ r1_tarski(esk2_2(esk4_0,X1),X1)
    | ~ v2_tex_2(X1,esk5_0)
    | ~ m1_subset_1(esk2_2(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_63]),c_0_15])])]),c_0_56]),c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk2_2(esk4_0,esk3_2(esk5_0,esk6_0)),esk3_2(esk5_0,esk6_0))
    | v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( v2_tex_2(esk3_2(esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_66])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk3_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_66])])).

cnf(c_0_74,negated_conjecture,
    ( v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)
    | m1_subset_1(esk2_2(esk4_0,esk3_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_66])])).

cnf(c_0_75,negated_conjecture,
    ( esk3_2(esk5_0,esk6_0) = esk6_0
    | ~ v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_66])])).

cnf(c_0_76,negated_conjecture,
    ( v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73])]),c_0_74])).

cnf(c_0_77,plain,
    ( v3_tex_2(X1,X2)
    | X1 != esk3_2(X2,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_78,negated_conjecture,
    ( esk3_2(esk5_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_66]),c_0_25]),c_0_52]),c_0_17])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.028 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t45_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&X3=X4)&v3_tex_2(X3,X1))=>v3_tex_2(X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tex_2)).
% 0.19/0.42  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.19/0.42  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.42  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 0.19/0.42  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.42  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 0.19/0.42  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&X3=X4)&v3_tex_2(X3,X1))=>v3_tex_2(X4,X2))))))), inference(assume_negation,[status(cth)],[t45_tex_2])).
% 0.19/0.42  fof(c_0_7, plain, ![X8, X9, X10, X11]:((X8=X10|g1_pre_topc(X8,X9)!=g1_pre_topc(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))))&(X9=X11|g1_pre_topc(X8,X9)!=g1_pre_topc(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.19/0.42  fof(c_0_8, negated_conjecture, (l1_pre_topc(esk4_0)&(l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(((g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))&esk6_0=esk7_0)&v3_tex_2(esk6_0,esk4_0))&~v3_tex_2(esk7_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.42  cnf(c_0_9, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.42  cnf(c_0_10, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_11, negated_conjecture, (X1=u1_pre_topc(esk5_0)|g1_pre_topc(X2,X1)!=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.42  fof(c_0_12, plain, ![X7]:(~l1_pre_topc(X7)|m1_subset_1(u1_pre_topc(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.42  cnf(c_0_13, negated_conjecture, (u1_pre_topc(esk5_0)=u1_pre_topc(esk4_0)|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(er,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_14, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_16, negated_conjecture, (u1_pre_topc(esk5_0)=u1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.19/0.42  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_18, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.42  cnf(c_0_19, negated_conjecture, (g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk4_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(rw,[status(thm)],[c_0_10, c_0_16])).
% 0.19/0.42  cnf(c_0_20, negated_conjecture, (m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_16]), c_0_17])])).
% 0.19/0.42  fof(c_0_21, plain, ![X12, X13, X14, X17]:(((m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))|~r1_tarski(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&((v3_pre_topc(esk1_3(X12,X13,X14),X12)|~r1_tarski(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(k9_subset_1(u1_struct_0(X12),X13,esk1_3(X12,X13,X14))=X14|~r1_tarski(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))))&((m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&((r1_tarski(esk2_2(X12,X13),X13)|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X12)))|(~v3_pre_topc(X17,X12)|k9_subset_1(u1_struct_0(X12),X13,X17)!=esk2_2(X12,X13))|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.19/0.42  cnf(c_0_22, negated_conjecture, (u1_struct_0(esk5_0)=X1|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=g1_pre_topc(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.19/0.42  fof(c_0_23, plain, ![X5, X6]:((~v3_pre_topc(X6,X5)|r2_hidden(X6,u1_pre_topc(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))&(~r2_hidden(X6,u1_pre_topc(X5))|v3_pre_topc(X6,X5)|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.42  cnf(c_0_24, plain, (v2_tex_2(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=esk2_2(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_25, negated_conjecture, (u1_struct_0(esk5_0)=u1_struct_0(esk4_0)), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_26, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_27, plain, (r1_tarski(esk2_2(X1,X2),X2)|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_28, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_29, negated_conjecture, (v2_tex_2(X1,esk5_0)|k9_subset_1(u1_struct_0(esk4_0),X1,X2)!=esk2_2(esk5_0,X1)|~v3_pre_topc(X2,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_17])])).
% 0.19/0.42  cnf(c_0_30, plain, (k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_31, negated_conjecture, (v2_tex_2(X1,esk5_0)|m1_subset_1(esk2_2(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_25]), c_0_17])])).
% 0.19/0.42  cnf(c_0_32, negated_conjecture, (r1_tarski(esk2_2(esk5_0,X1),X1)|v2_tex_2(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_17])])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (v3_pre_topc(X1,esk5_0)|~r2_hidden(X1,u1_pre_topc(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_16]), c_0_17])]), c_0_25])).
% 0.19/0.42  cnf(c_0_34, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  fof(c_0_35, plain, ![X18, X19, X20]:(((v2_tex_2(X19,X18)|~v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~v2_tex_2(X20,X18)|~r1_tarski(X19,X20)|X19=X20)|~v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18)))&((m1_subset_1(esk3_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|~v2_tex_2(X19,X18)|v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(((v2_tex_2(esk3_2(X18,X19),X18)|~v2_tex_2(X19,X18)|v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(r1_tarski(X19,esk3_2(X18,X19))|~v2_tex_2(X19,X18)|v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18)))&(X19!=esk3_2(X18,X19)|~v2_tex_2(X19,X18)|v3_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_37, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (~v3_tex_2(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_39, negated_conjecture, (v2_tex_2(X1,esk5_0)|~v2_tex_2(X1,esk4_0)|~v3_pre_topc(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),esk5_0)|~m1_subset_1(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_15])])]), c_0_31]), c_0_32])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (v3_pre_topc(X1,esk5_0)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_15])])).
% 0.19/0.42  cnf(c_0_41, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (~v3_tex_2(esk6_0,esk5_0)), inference(rw,[status(thm)],[c_0_38, c_0_37])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (v2_tex_2(X1,esk5_0)|~v2_tex_2(X1,esk4_0)|~v3_pre_topc(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),esk4_0)|~m1_subset_1(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.42  cnf(c_0_45, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk4_0))|~v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_16]), c_0_17])]), c_0_25])).
% 0.19/0.42  cnf(c_0_47, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk3_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~v2_tex_2(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_17])]), c_0_43])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (v2_tex_2(X1,esk5_0)|~v2_tex_2(X1,esk4_0)|~m1_subset_1(esk1_3(esk4_0,X1,esk2_2(esk5_0,X1)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_15])]), c_0_31]), c_0_32])).
% 0.19/0.42  cnf(c_0_50, plain, (v2_tex_2(X1,X2)|~v3_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_51, negated_conjecture, (v3_tex_2(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_53, plain, (X3=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X1,X2)|~r1_tarski(X3,X1)|~v3_tex_2(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_54, plain, (r1_tarski(X1,esk3_2(X2,X1))|v3_tex_2(X1,X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, (v3_pre_topc(X1,esk4_0)|~v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_46]), c_0_15])])).
% 0.19/0.42  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk1_3(esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X2,X1)|~v2_tex_2(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_25]), c_0_17])])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk3_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tex_2(esk6_0,esk5_0)), inference(rw,[status(thm)],[c_0_48, c_0_25])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, (v2_tex_2(X1,esk5_0)|~v2_tex_2(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_15])]), c_0_31]), c_0_32])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (v2_tex_2(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_15])]), c_0_52])])).
% 0.19/0.42  cnf(c_0_60, plain, (v2_tex_2(esk3_2(X1,X2),X1)|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (X1=esk6_0|~r1_tarski(esk6_0,X1)|~v2_tex_2(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_51]), c_0_15])])).
% 0.19/0.42  cnf(c_0_62, negated_conjecture, (r1_tarski(esk6_0,esk3_2(esk5_0,esk6_0))|~v2_tex_2(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_42]), c_0_17])]), c_0_43])).
% 0.19/0.42  cnf(c_0_63, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),X1,esk1_3(esk5_0,X1,X2))=X2|~r1_tarski(X2,X1)|~v2_tex_2(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_25]), c_0_17])])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (v3_pre_topc(esk1_3(esk5_0,X1,X2),esk4_0)|~r1_tarski(X2,X1)|~v2_tex_2(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_45]), c_0_25]), c_0_25]), c_0_17])]), c_0_56])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (r1_tarski(esk2_2(esk4_0,esk3_2(esk5_0,esk6_0)),esk3_2(esk5_0,esk6_0))|v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)|~v2_tex_2(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_57]), c_0_15])])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (v2_tex_2(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_52]), c_0_59])])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (v2_tex_2(esk3_2(esk5_0,esk6_0),esk5_0)|~v2_tex_2(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_42]), c_0_17])]), c_0_43])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)|m1_subset_1(esk2_2(esk4_0,esk3_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~v2_tex_2(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_57]), c_0_15])])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (esk3_2(esk5_0,esk6_0)=esk6_0|~v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)|~v2_tex_2(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_57])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (v2_tex_2(X1,esk4_0)|~r1_tarski(esk2_2(esk4_0,X1),X1)|~v2_tex_2(X1,esk5_0)|~m1_subset_1(esk2_2(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_63]), c_0_15])])]), c_0_56]), c_0_64])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (r1_tarski(esk2_2(esk4_0,esk3_2(esk5_0,esk6_0)),esk3_2(esk5_0,esk6_0))|v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (v2_tex_2(esk3_2(esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_66])])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk3_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_66])])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)|m1_subset_1(esk2_2(esk4_0,esk3_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_66])])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (esk3_2(esk5_0,esk6_0)=esk6_0|~v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_66])])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (v2_tex_2(esk3_2(esk5_0,esk6_0),esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73])]), c_0_74])).
% 0.19/0.42  cnf(c_0_77, plain, (v3_tex_2(X1,X2)|X1!=esk3_2(X2,X1)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (esk3_2(esk5_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_66]), c_0_25]), c_0_52]), c_0_17])]), c_0_43]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 80
% 0.19/0.42  # Proof object clause steps            : 67
% 0.19/0.42  # Proof object formula steps           : 13
% 0.19/0.42  # Proof object conjectures             : 53
% 0.19/0.42  # Proof object clause conjectures      : 50
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 25
% 0.19/0.42  # Proof object initial formulas used   : 6
% 0.19/0.42  # Proof object generating inferences   : 32
% 0.19/0.42  # Proof object simplifying inferences  : 98
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 6
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 25
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 25
% 0.19/0.42  # Processed clauses                    : 294
% 0.19/0.42  # ...of these trivial                  : 4
% 0.19/0.42  # ...subsumed                          : 31
% 0.19/0.42  # ...remaining for further processing  : 259
% 0.19/0.42  # Other redundant clauses eliminated   : 2
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 3
% 0.19/0.42  # Backward-rewritten                   : 145
% 0.19/0.42  # Generated clauses                    : 936
% 0.19/0.42  # ...of the previous two non-trivial   : 983
% 0.19/0.42  # Contextual simplify-reflections      : 24
% 0.19/0.42  # Paramodulations                      : 928
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 8
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 86
% 0.19/0.42  #    Positive orientable unit clauses  : 11
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 1
% 0.19/0.42  #    Non-unit-clauses                  : 74
% 0.19/0.42  # Current number of unprocessed clauses: 656
% 0.19/0.42  # ...number of literals in the above   : 4056
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 173
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 7969
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 1082
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 56
% 0.19/0.42  # Unit Clause-clause subsumption calls : 61
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 7
% 0.19/0.42  # BW rewrite match successes           : 5
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 46847
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.079 s
% 0.19/0.42  # System time              : 0.004 s
% 0.19/0.42  # Total time               : 0.083 s
% 0.19/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
