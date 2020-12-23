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
% DateTime   : Thu Dec  3 11:19:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 548 expanded)
%              Number of clauses        :   36 ( 226 expanded)
%              Number of leaves         :    5 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :  192 (2795 expanded)
%              Number of equality atoms :   33 ( 780 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_tex_2,conjecture,(
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
                      & v2_tex_2(X3,X1) )
                   => v2_tex_2(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_5,negated_conjecture,(
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
                        & v2_tex_2(X3,X1) )
                     => v2_tex_2(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_tex_2])).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X8 = X10
        | g1_pre_topc(X8,X9) != g1_pre_topc(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) )
      & ( X9 = X11
        | g1_pre_topc(X8,X9) != g1_pre_topc(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_7,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    & esk5_0 = esk6_0
    & v2_tex_2(esk5_0,esk3_0)
    & ~ v2_tex_2(esk6_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( u1_pre_topc(esk4_0) = X1
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != g1_pre_topc(X2,X1)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_11,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | m1_subset_1(u1_pre_topc(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_12,negated_conjecture,
    ( u1_pre_topc(esk4_0) = u1_pre_topc(esk3_0)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( u1_pre_topc(esk4_0) = u1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_16,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_15]),c_0_14])])).

fof(c_0_19,plain,(
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

cnf(c_0_20,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != g1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_21,plain,(
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

cnf(c_0_22,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk2_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk3_0) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v2_tex_2(X1,esk4_0)
    | k9_subset_1(u1_struct_0(esk3_0),X1,X2) != esk2_2(esk4_0,X1)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_14])])).

cnf(c_0_28,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( v2_tex_2(X1,esk4_0)
    | m1_subset_1(esk2_2(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_14])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk2_2(esk4_0,X1),X1)
    | v2_tex_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_14])])).

cnf(c_0_32,negated_conjecture,
    ( v3_pre_topc(X1,esk4_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_15]),c_0_14])]),c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( v2_tex_2(X1,esk4_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ v3_pre_topc(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),esk4_0)
    | ~ m1_subset_1(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])]),c_0_30]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v3_pre_topc(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( v2_tex_2(X1,esk4_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ v3_pre_topc(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),esk3_0)
    | ~ m1_subset_1(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( v2_tex_2(X1,esk4_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,negated_conjecture,
    ( v2_tex_2(X1,esk4_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_44,negated_conjecture,
    ( v2_tex_2(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.032 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t25_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&X3=X4)&v2_tex_2(X3,X1))=>v2_tex_2(X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tex_2)).
% 0.19/0.40  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.19/0.40  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.40  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 0.19/0.40  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.40  fof(c_0_5, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&X3=X4)&v2_tex_2(X3,X1))=>v2_tex_2(X4,X2))))))), inference(assume_negation,[status(cth)],[t25_tex_2])).
% 0.19/0.40  fof(c_0_6, plain, ![X8, X9, X10, X11]:((X8=X10|g1_pre_topc(X8,X9)!=g1_pre_topc(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))))&(X9=X11|g1_pre_topc(X8,X9)!=g1_pre_topc(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.19/0.40  fof(c_0_7, negated_conjecture, (l1_pre_topc(esk3_0)&(l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(((g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))&esk5_0=esk6_0)&v2_tex_2(esk5_0,esk3_0))&~v2_tex_2(esk6_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.40  cnf(c_0_8, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_9, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_10, negated_conjecture, (u1_pre_topc(esk4_0)=X1|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=g1_pre_topc(X2,X1)|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.40  fof(c_0_11, plain, ![X7]:(~l1_pre_topc(X7)|m1_subset_1(u1_pre_topc(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.40  cnf(c_0_12, negated_conjecture, (u1_pre_topc(esk4_0)=u1_pre_topc(esk3_0)|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(er,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_13, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_15, negated_conjecture, (u1_pre_topc(esk4_0)=u1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.19/0.40  cnf(c_0_16, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(rw,[status(thm)],[c_0_9, c_0_15])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_15]), c_0_14])])).
% 0.19/0.40  fof(c_0_19, plain, ![X12, X13, X14, X17]:(((m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))|~r1_tarski(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&((v3_pre_topc(esk1_3(X12,X13,X14),X12)|~r1_tarski(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(k9_subset_1(u1_struct_0(X12),X13,esk1_3(X12,X13,X14))=X14|~r1_tarski(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))))&((m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&((r1_tarski(esk2_2(X12,X13),X13)|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X12)))|(~v3_pre_topc(X17,X12)|k9_subset_1(u1_struct_0(X12),X13,X17)!=esk2_2(X12,X13))|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (u1_struct_0(esk4_0)=X1|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=g1_pre_topc(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.19/0.40  fof(c_0_21, plain, ![X5, X6]:((~v3_pre_topc(X6,X5)|r2_hidden(X6,u1_pre_topc(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))&(~r2_hidden(X6,u1_pre_topc(X5))|v3_pre_topc(X6,X5)|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.40  cnf(c_0_22, plain, (v2_tex_2(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=esk2_2(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk3_0)), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_24, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_25, plain, (r1_tarski(esk2_2(X1,X2),X2)|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_26, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (v2_tex_2(X1,esk4_0)|k9_subset_1(u1_struct_0(esk3_0),X1,X2)!=esk2_2(esk4_0,X1)|~v3_pre_topc(X2,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_14])])).
% 0.19/0.40  cnf(c_0_28, plain, (k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (v2_tex_2(X1,esk4_0)|m1_subset_1(esk2_2(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_14])])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (r1_tarski(esk2_2(esk4_0,X1),X1)|v2_tex_2(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_14])])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (v3_pre_topc(X1,esk4_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_15]), c_0_14])]), c_0_23])).
% 0.19/0.40  cnf(c_0_33, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (v2_tex_2(X1,esk4_0)|~v2_tex_2(X1,esk3_0)|~v3_pre_topc(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),esk4_0)|~m1_subset_1(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])]), c_0_30]), c_0_31])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (v3_pre_topc(X1,esk4_0)|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_29])])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (v2_tex_2(X1,esk4_0)|~v2_tex_2(X1,esk3_0)|~v3_pre_topc(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),esk3_0)|~m1_subset_1(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.40  cnf(c_0_37, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (v2_tex_2(X1,esk4_0)|~v2_tex_2(X1,esk3_0)|~m1_subset_1(esk1_3(esk3_0,X1,esk2_2(esk4_0,X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29])]), c_0_30]), c_0_31])).
% 0.19/0.40  cnf(c_0_39, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (~v2_tex_2(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (esk5_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (v2_tex_2(X1,esk4_0)|~v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_29])]), c_0_30]), c_0_31])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v2_tex_2(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])]), c_0_45]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 47
% 0.19/0.40  # Proof object clause steps            : 36
% 0.19/0.40  # Proof object formula steps           : 11
% 0.19/0.40  # Proof object conjectures             : 28
% 0.19/0.40  # Proof object clause conjectures      : 25
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 18
% 0.19/0.40  # Proof object initial formulas used   : 5
% 0.19/0.40  # Proof object generating inferences   : 16
% 0.19/0.40  # Proof object simplifying inferences  : 35
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 5
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 19
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 19
% 0.19/0.40  # Processed clauses                    : 168
% 0.19/0.40  # ...of these trivial                  : 1
% 0.19/0.40  # ...subsumed                          : 9
% 0.19/0.40  # ...remaining for further processing  : 158
% 0.19/0.40  # Other redundant clauses eliminated   : 2
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 3
% 0.19/0.40  # Backward-rewritten                   : 9
% 0.19/0.40  # Generated clauses                    : 523
% 0.19/0.40  # ...of the previous two non-trivial   : 483
% 0.19/0.40  # Contextual simplify-reflections      : 7
% 0.19/0.40  # Paramodulations                      : 515
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 8
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 127
% 0.19/0.40  #    Positive orientable unit clauses  : 10
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 1
% 0.19/0.40  #    Non-unit-clauses                  : 116
% 0.19/0.40  # Current number of unprocessed clauses: 345
% 0.19/0.40  # ...number of literals in the above   : 2267
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 31
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 3394
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 345
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.40  # Unit Clause-clause subsumption calls : 0
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 4
% 0.19/0.40  # BW rewrite match successes           : 2
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 27228
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.057 s
% 0.19/0.40  # System time              : 0.010 s
% 0.19/0.40  # Total time               : 0.067 s
% 0.19/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
