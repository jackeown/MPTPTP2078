%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:14 EST 2020

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 646 expanded)
%              Number of clauses        :   52 ( 253 expanded)
%              Number of leaves         :    9 ( 158 expanded)
%              Depth                    :   12
%              Number of atoms          :  315 (4231 expanded)
%              Number of equality atoms :   23 ( 946 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t52_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t44_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_pre_topc)).

fof(t46_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ? [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
              & ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X4,X3)
                  <=> ( v4_pre_topc(X4,X1)
                      & r1_tarski(X2,X4) ) ) )
              & k2_pre_topc(X1,X2) = k6_setfam_1(u1_struct_0(X1),X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t45_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( r2_hidden(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v4_pre_topc(X4,X1)
                        & r1_tarski(X2,X4) )
                     => r2_hidden(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_9,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | r1_tarski(X31,k2_pre_topc(X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v4_pre_topc(X2,X1)
               => k2_pre_topc(X1,X2) = X2 )
              & ( ( v2_pre_topc(X1)
                  & k2_pre_topc(X1,X2) = X2 )
               => v4_pre_topc(X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_pre_topc])).

cnf(c_0_12,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( v2_pre_topc(esk5_0)
      | v4_pre_topc(esk6_0,esk5_0) )
    & ( k2_pre_topc(esk5_0,esk6_0) = esk6_0
      | v4_pre_topc(esk6_0,esk5_0) )
    & ( ~ v4_pre_topc(esk6_0,esk5_0)
      | v4_pre_topc(esk6_0,esk5_0) )
    & ( v2_pre_topc(esk5_0)
      | k2_pre_topc(esk5_0,esk6_0) != esk6_0 )
    & ( k2_pre_topc(esk5_0,esk6_0) = esk6_0
      | k2_pre_topc(esk5_0,esk6_0) != esk6_0 )
    & ( ~ v4_pre_topc(esk6_0,esk5_0)
      | k2_pre_topc(esk5_0,esk6_0) != esk6_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | m1_subset_1(k2_pre_topc(X16,X17),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X2,k2_pre_topc(X3,X1))
    | ~ r1_tarski(k2_pre_topc(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk5_0)
    | k2_pre_topc(esk5_0,esk6_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ( m1_subset_1(esk2_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X18),X19),X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X18),X19),X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ v4_pre_topc(esk2_2(X18,X19),X18)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X18),X19),X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_pre_topc])])])])])).

fof(c_0_22,plain,(
    ! [X26,X27,X29] :
      ( ( m1_subset_1(esk4_2(X26,X27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( v4_pre_topc(X29,X26)
        | ~ r2_hidden(X29,esk4_2(X26,X27))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r1_tarski(X27,X29)
        | ~ r2_hidden(X29,esk4_2(X26,X27))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ v4_pre_topc(X29,X26)
        | ~ r1_tarski(X27,X29)
        | r2_hidden(X29,esk4_2(X26,X27))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( k2_pre_topc(X26,X27) = k6_setfam_1(u1_struct_0(X26),esk4_2(X26,X27))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_pre_topc])])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk5_0)
    | k2_pre_topc(esk5_0,esk6_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r1_tarski(X1,k2_pre_topc(esk5_0,esk6_0))
    | ~ r1_tarski(k2_pre_topc(esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k2_pre_topc(esk5_0,X1) != X1
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ r1_tarski(esk6_0,X1)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_28,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_pre_topc(X1,X2) = k6_setfam_1(u1_struct_0(X1),esk4_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v4_pre_topc(X1,X2)
    | ~ r2_hidden(X1,esk4_2(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_18])])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk5_0)
    | ~ r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)
    | ~ r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_13])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_26])])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( ~ v4_pre_topc(X1,esk5_0)
    | ~ r1_tarski(X1,k2_pre_topc(esk5_0,X1))
    | ~ r1_tarski(k2_pre_topc(esk5_0,X1),X1)
    | ~ r1_tarski(esk6_0,X1)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_13])])).

cnf(c_0_37,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v4_pre_topc(esk2_2(X1,esk4_2(X1,X2)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k2_pre_topc(esk5_0,esk6_0) = esk6_0
    | v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk5_0)
    | v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( v4_pre_topc(X1,esk5_0)
    | ~ v2_pre_topc(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,esk4_2(esk5_0,k2_pre_topc(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_18])])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk5_0)
    | ~ r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_42,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | m1_subset_1(esk2_2(X1,esk4_2(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( ~ v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_pre_topc(esk5_0,X1),X1)
    | ~ r1_tarski(esk6_0,X1)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_12]),c_0_18])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | ~ v4_pre_topc(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_18]),c_0_17])]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,esk4_2(esk5_0,k2_pre_topc(esk5_0,esk6_0)))
    | ~ r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_38]),c_0_18]),c_0_17])]),c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_17]),c_0_26])])).

cnf(c_0_49,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | r2_hidden(esk2_2(X1,esk4_2(X1,X2)),esk4_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_30])).

fof(c_0_50,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_51,plain,(
    ! [X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X23,k2_pre_topc(X21,X22))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v4_pre_topc(X24,X21)
        | ~ r1_tarski(X22,X24)
        | r2_hidden(X23,X24)
        | ~ r2_hidden(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk3_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | r2_hidden(X23,k2_pre_topc(X21,X22))
        | ~ r2_hidden(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( v4_pre_topc(esk3_3(X21,X22,X23),X21)
        | r2_hidden(X23,k2_pre_topc(X21,X22))
        | ~ r2_hidden(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( r1_tarski(X22,esk3_3(X21,X22,X23))
        | r2_hidden(X23,k2_pre_topc(X21,X22))
        | ~ r2_hidden(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(X23,esk3_3(X21,X22,X23))
        | r2_hidden(X23,k2_pre_topc(X21,X22))
        | ~ r2_hidden(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk4_2(esk5_0,k2_pre_topc(esk5_0,esk6_0)))
    | ~ r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( X1 = esk6_0
    | v4_pre_topc(esk6_0,esk5_0)
    | ~ r1_tarski(k2_pre_topc(esk5_0,esk6_0),X1)
    | ~ r1_tarski(X1,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0)
    | r2_hidden(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk4_2(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_18]),c_0_17])]),c_0_39])).

fof(c_0_55,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | ~ r2_hidden(X15,X14)
      | r2_hidden(X15,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_56,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)
    | ~ r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_13])])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_26]),c_0_26])]),c_0_54])).

cnf(c_0_60,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,X2))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ r1_tarski(X2,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_17]),c_0_18])]),c_0_59])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_32])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),k2_pre_topc(esk5_0,esk6_0))
    | ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_12]),c_0_18]),c_0_17])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk5_0)
    | ~ r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_17]),c_0_26])]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),k2_pre_topc(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_59])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:44:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.06/1.25  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 1.06/1.25  # and selection function PSelectUnlessUniqMaxPos.
% 1.06/1.25  #
% 1.06/1.25  # Preprocessing time       : 0.029 s
% 1.06/1.25  # Presaturation interreduction done
% 1.06/1.25  
% 1.06/1.25  # Proof found!
% 1.06/1.25  # SZS status Theorem
% 1.06/1.25  # SZS output start CNFRefutation
% 1.06/1.25  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 1.06/1.25  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.06/1.25  fof(t52_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 1.06/1.25  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 1.06/1.25  fof(t44_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v4_pre_topc(X3,X1)))=>v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_pre_topc)).
% 1.06/1.25  fof(t46_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>?[X3]:((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>(v4_pre_topc(X4,X1)&r1_tarski(X2,X4)))))&k2_pre_topc(X1,X2)=k6_setfam_1(u1_struct_0(X1),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_pre_topc)).
% 1.06/1.25  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.06/1.25  fof(t45_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(r2_hidden(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X4,X1)&r1_tarski(X2,X4))=>r2_hidden(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_pre_topc)).
% 1.06/1.25  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.06/1.25  fof(c_0_9, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|r1_tarski(X31,k2_pre_topc(X30,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 1.06/1.25  fof(c_0_10, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.06/1.25  fof(c_0_11, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1)))))), inference(assume_negation,[status(cth)],[t52_pre_topc])).
% 1.06/1.25  cnf(c_0_12, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.06/1.25  cnf(c_0_13, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.06/1.25  fof(c_0_14, negated_conjecture, (l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&((((v2_pre_topc(esk5_0)|v4_pre_topc(esk6_0,esk5_0))&(k2_pre_topc(esk5_0,esk6_0)=esk6_0|v4_pre_topc(esk6_0,esk5_0)))&(~v4_pre_topc(esk6_0,esk5_0)|v4_pre_topc(esk6_0,esk5_0)))&(((v2_pre_topc(esk5_0)|k2_pre_topc(esk5_0,esk6_0)!=esk6_0)&(k2_pre_topc(esk5_0,esk6_0)=esk6_0|k2_pre_topc(esk5_0,esk6_0)!=esk6_0))&(~v4_pre_topc(esk6_0,esk5_0)|k2_pre_topc(esk5_0,esk6_0)!=esk6_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 1.06/1.25  fof(c_0_15, plain, ![X16, X17]:(~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|m1_subset_1(k2_pre_topc(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 1.06/1.25  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(X2,k2_pre_topc(X3,X1))|~r1_tarski(k2_pre_topc(X3,X1),X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 1.06/1.25  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.06/1.25  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.06/1.25  cnf(c_0_19, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.06/1.25  cnf(c_0_20, negated_conjecture, (~v4_pre_topc(esk6_0,esk5_0)|k2_pre_topc(esk5_0,esk6_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.06/1.25  fof(c_0_21, plain, ![X18, X19]:((m1_subset_1(esk2_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|v4_pre_topc(k6_setfam_1(u1_struct_0(X18),X19),X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&((r2_hidden(esk2_2(X18,X19),X19)|v4_pre_topc(k6_setfam_1(u1_struct_0(X18),X19),X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~v4_pre_topc(esk2_2(X18,X19),X18)|v4_pre_topc(k6_setfam_1(u1_struct_0(X18),X19),X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_pre_topc])])])])])).
% 1.06/1.25  fof(c_0_22, plain, ![X26, X27, X29]:(((m1_subset_1(esk4_2(X26,X27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(((v4_pre_topc(X29,X26)|~r2_hidden(X29,esk4_2(X26,X27))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(r1_tarski(X27,X29)|~r2_hidden(X29,esk4_2(X26,X27))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26))))&(~v4_pre_topc(X29,X26)|~r1_tarski(X27,X29)|r2_hidden(X29,esk4_2(X26,X27))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))))&(k2_pre_topc(X26,X27)=k6_setfam_1(u1_struct_0(X26),esk4_2(X26,X27))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_pre_topc])])])])])).
% 1.06/1.25  cnf(c_0_23, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.06/1.25  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk5_0)|k2_pre_topc(esk5_0,esk6_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.06/1.25  cnf(c_0_25, negated_conjecture, (r1_tarski(esk6_0,X1)|~r1_tarski(X1,k2_pre_topc(esk5_0,esk6_0))|~r1_tarski(k2_pre_topc(esk5_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 1.06/1.25  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_19])).
% 1.06/1.25  cnf(c_0_27, negated_conjecture, (k2_pre_topc(esk5_0,X1)!=X1|~v4_pre_topc(X1,esk5_0)|~r1_tarski(esk6_0,X1)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_13])).
% 1.06/1.25  cnf(c_0_28, plain, (v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)|~v4_pre_topc(esk2_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.06/1.25  cnf(c_0_29, plain, (k2_pre_topc(X1,X2)=k6_setfam_1(u1_struct_0(X1),esk4_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.06/1.25  cnf(c_0_30, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.06/1.25  cnf(c_0_31, plain, (v4_pre_topc(X1,X2)|~r2_hidden(X1,esk4_2(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.06/1.25  cnf(c_0_32, negated_conjecture, (m1_subset_1(k2_pre_topc(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_17]), c_0_18])])).
% 1.06/1.25  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk5_0)|~r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)|~r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_13])])).
% 1.06/1.25  cnf(c_0_34, negated_conjecture, (r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_26])])).
% 1.06/1.25  cnf(c_0_35, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.06/1.25  cnf(c_0_36, negated_conjecture, (~v4_pre_topc(X1,esk5_0)|~r1_tarski(X1,k2_pre_topc(esk5_0,X1))|~r1_tarski(k2_pre_topc(esk5_0,X1),X1)|~r1_tarski(esk6_0,X1)|~r1_tarski(X1,esk6_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_13])])).
% 1.06/1.25  cnf(c_0_37, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v4_pre_topc(esk2_2(X1,esk4_2(X1,X2)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 1.06/1.25  cnf(c_0_38, negated_conjecture, (k2_pre_topc(esk5_0,esk6_0)=esk6_0|v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.06/1.25  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk5_0)|v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.06/1.25  cnf(c_0_40, negated_conjecture, (v4_pre_topc(X1,esk5_0)|~v2_pre_topc(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X1,esk4_2(esk5_0,k2_pre_topc(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_18])])).
% 1.06/1.25  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk5_0)|~r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 1.06/1.25  cnf(c_0_42, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|m1_subset_1(esk2_2(X1,esk4_2(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_30])).
% 1.06/1.25  cnf(c_0_43, negated_conjecture, (~v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_pre_topc(esk5_0,X1),X1)|~r1_tarski(esk6_0,X1)|~r1_tarski(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_12]), c_0_18])])).
% 1.06/1.25  cnf(c_0_44, plain, (r2_hidden(esk2_2(X1,X2),X2)|v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.06/1.25  cnf(c_0_45, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|~v4_pre_topc(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_18]), c_0_17])]), c_0_39])).
% 1.06/1.25  cnf(c_0_46, negated_conjecture, (v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X1,esk4_2(esk5_0,k2_pre_topc(esk5_0,esk6_0)))|~r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.06/1.25  cnf(c_0_47, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|m1_subset_1(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_38]), c_0_18]), c_0_17])]), c_0_39])).
% 1.06/1.25  cnf(c_0_48, negated_conjecture, (~v4_pre_topc(esk6_0,esk5_0)|~r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_17]), c_0_26])])).
% 1.06/1.25  cnf(c_0_49, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|r2_hidden(esk2_2(X1,esk4_2(X1,X2)),esk4_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_30])).
% 1.06/1.25  fof(c_0_50, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.06/1.25  fof(c_0_51, plain, ![X21, X22, X23, X24]:((~r2_hidden(X23,k2_pre_topc(X21,X22))|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|(~v4_pre_topc(X24,X21)|~r1_tarski(X22,X24)|r2_hidden(X23,X24)))|~r2_hidden(X23,u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&((m1_subset_1(esk3_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))|r2_hidden(X23,k2_pre_topc(X21,X22))|~r2_hidden(X23,u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(((v4_pre_topc(esk3_3(X21,X22,X23),X21)|r2_hidden(X23,k2_pre_topc(X21,X22))|~r2_hidden(X23,u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(r1_tarski(X22,esk3_3(X21,X22,X23))|r2_hidden(X23,k2_pre_topc(X21,X22))|~r2_hidden(X23,u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21)))&(~r2_hidden(X23,esk3_3(X21,X22,X23))|r2_hidden(X23,k2_pre_topc(X21,X22))|~r2_hidden(X23,u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).
% 1.06/1.25  cnf(c_0_52, negated_conjecture, (~r2_hidden(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk4_2(esk5_0,k2_pre_topc(esk5_0,esk6_0)))|~r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])).
% 1.06/1.25  cnf(c_0_53, negated_conjecture, (X1=esk6_0|v4_pre_topc(esk6_0,esk5_0)|~r1_tarski(k2_pre_topc(esk5_0,esk6_0),X1)|~r1_tarski(X1,k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_13])).
% 1.06/1.25  cnf(c_0_54, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)|r2_hidden(esk2_2(esk5_0,esk4_2(esk5_0,esk6_0)),esk4_2(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_18]), c_0_17])]), c_0_39])).
% 1.06/1.25  fof(c_0_55, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|(~r2_hidden(X15,X14)|r2_hidden(X15,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 1.06/1.25  cnf(c_0_56, negated_conjecture, (~v4_pre_topc(esk6_0,esk5_0)|~r1_tarski(k2_pre_topc(esk5_0,esk6_0),esk6_0)|~r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_13])])).
% 1.06/1.25  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.06/1.25  cnf(c_0_58, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X4,X2)|~r1_tarski(X3,X4)|~r2_hidden(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.06/1.25  cnf(c_0_59, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_26]), c_0_26])]), c_0_54])).
% 1.06/1.25  cnf(c_0_60, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.06/1.25  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),k2_pre_topc(esk5_0,esk6_0))|~v4_pre_topc(esk6_0,esk5_0)|~r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.06/1.25  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.06/1.25  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,esk6_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X1,k2_pre_topc(esk5_0,X2))|~r2_hidden(X1,u1_struct_0(esk5_0))|~r1_tarski(X2,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_17]), c_0_18])]), c_0_59])])).
% 1.06/1.25  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_60, c_0_32])).
% 1.06/1.25  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),k2_pre_topc(esk5_0,esk6_0))|~v4_pre_topc(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_12]), c_0_18]), c_0_17])])).
% 1.06/1.25  cnf(c_0_66, negated_conjecture, (~v4_pre_topc(esk6_0,esk5_0)|~r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_62])).
% 1.06/1.25  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k2_pre_topc(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_17]), c_0_26])]), c_0_64])).
% 1.06/1.25  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),k2_pre_topc(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_59])])).
% 1.06/1.25  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk1_2(k2_pre_topc(esk5_0,esk6_0),esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_59])])).
% 1.06/1.25  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), ['proof']).
% 1.06/1.25  # SZS output end CNFRefutation
% 1.06/1.25  # Proof object total steps             : 71
% 1.06/1.25  # Proof object clause steps            : 52
% 1.06/1.25  # Proof object formula steps           : 19
% 1.06/1.25  # Proof object conjectures             : 36
% 1.06/1.25  # Proof object clause conjectures      : 33
% 1.06/1.25  # Proof object formula conjectures     : 3
% 1.06/1.25  # Proof object initial clauses used    : 20
% 1.06/1.25  # Proof object initial formulas used   : 9
% 1.06/1.25  # Proof object generating inferences   : 28
% 1.06/1.25  # Proof object simplifying inferences  : 54
% 1.06/1.25  # Training examples: 0 positive, 0 negative
% 1.06/1.25  # Parsed axioms                        : 9
% 1.06/1.25  # Removed by relevancy pruning/SinE    : 0
% 1.06/1.25  # Initial clauses                      : 30
% 1.06/1.25  # Removed in clause preprocessing      : 2
% 1.06/1.25  # Initial clauses in saturation        : 28
% 1.06/1.25  # Processed clauses                    : 8180
% 1.06/1.25  # ...of these trivial                  : 19
% 1.06/1.25  # ...subsumed                          : 6239
% 1.06/1.25  # ...remaining for further processing  : 1922
% 1.06/1.25  # Other redundant clauses eliminated   : 85
% 1.06/1.25  # Clauses deleted for lack of memory   : 0
% 1.06/1.25  # Backward-subsumed                    : 827
% 1.06/1.25  # Backward-rewritten                   : 187
% 1.06/1.25  # Generated clauses                    : 50081
% 1.06/1.25  # ...of the previous two non-trivial   : 46474
% 1.06/1.25  # Contextual simplify-reflections      : 54
% 1.06/1.25  # Paramodulations                      : 49982
% 1.06/1.25  # Factorizations                       : 14
% 1.06/1.25  # Equation resolutions                 : 85
% 1.06/1.25  # Propositional unsat checks           : 0
% 1.06/1.25  #    Propositional check models        : 0
% 1.06/1.25  #    Propositional check unsatisfiable : 0
% 1.06/1.25  #    Propositional clauses             : 0
% 1.06/1.25  #    Propositional clauses after purity: 0
% 1.06/1.25  #    Propositional unsat core size     : 0
% 1.06/1.25  #    Propositional preprocessing time  : 0.000
% 1.06/1.25  #    Propositional encoding time       : 0.000
% 1.06/1.25  #    Propositional solver time         : 0.000
% 1.06/1.25  #    Success case prop preproc time    : 0.000
% 1.06/1.25  #    Success case prop encoding time   : 0.000
% 1.06/1.25  #    Success case prop solver time     : 0.000
% 1.06/1.25  # Current number of processed clauses  : 879
% 1.06/1.25  #    Positive orientable unit clauses  : 34
% 1.06/1.25  #    Positive unorientable unit clauses: 0
% 1.06/1.25  #    Negative unit clauses             : 5
% 1.06/1.25  #    Non-unit-clauses                  : 840
% 1.06/1.25  # Current number of unprocessed clauses: 35250
% 1.06/1.25  # ...number of literals in the above   : 215072
% 1.06/1.25  # Current number of archived formulas  : 0
% 1.06/1.25  # Current number of archived clauses   : 1041
% 1.06/1.25  # Clause-clause subsumption calls (NU) : 309288
% 1.06/1.25  # Rec. Clause-clause subsumption calls : 66682
% 1.06/1.25  # Non-unit clause-clause subsumptions  : 6615
% 1.06/1.25  # Unit Clause-clause subsumption calls : 2819
% 1.06/1.25  # Rewrite failures with RHS unbound    : 0
% 1.06/1.25  # BW rewrite match attempts            : 342
% 1.06/1.25  # BW rewrite match successes           : 7
% 1.06/1.25  # Condensation attempts                : 0
% 1.06/1.25  # Condensation successes               : 0
% 1.06/1.25  # Termbank termtop insertions          : 1409315
% 1.06/1.25  
% 1.06/1.25  # -------------------------------------------------
% 1.06/1.25  # User time                : 0.896 s
% 1.06/1.25  # System time              : 0.025 s
% 1.06/1.25  # Total time               : 0.921 s
% 1.06/1.25  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
