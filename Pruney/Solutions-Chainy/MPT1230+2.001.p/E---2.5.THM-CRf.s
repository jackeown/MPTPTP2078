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
% DateTime   : Thu Dec  3 11:10:40 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 186 expanded)
%              Number of clauses        :   36 (  69 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  286 (2143 expanded)
%              Number of equality atoms :   25 ( 129 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   76 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_tops_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ~ ( v3_pre_topc(X4,X1)
                        & r2_hidden(X3,X4)
                        & r1_xboole_0(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tops_1)).

fof(d13_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k2_pre_topc(X1,X2)
              <=> ! [X4] :
                    ( r2_hidden(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v3_pre_topc(X5,X1)
                              & r2_hidden(X4,X5)
                              & r1_xboole_0(X2,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k2_pre_topc(X1,X2))
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ~ ( v3_pre_topc(X4,X1)
                          & r2_hidden(X3,X4)
                          & r1_xboole_0(X2,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_tops_1])).

fof(c_0_7,negated_conjecture,(
    ! [X25] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
      & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) )
      & ( v3_pre_topc(esk7_0,esk4_0)
        | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) )
      & ( r2_hidden(esk6_0,esk7_0)
        | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) )
      & ( r1_xboole_0(esk5_0,esk7_0)
        | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) )
      & ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v3_pre_topc(X25,esk4_0)
        | ~ r2_hidden(esk6_0,X25)
        | ~ r1_xboole_0(esk5_0,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X11,X12,X16] :
      ( ( ~ r2_hidden(X11,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_pre_topc(X12,X8)
        | ~ r2_hidden(X11,X12)
        | ~ r1_xboole_0(X9,X12)
        | ~ r2_hidden(X11,u1_struct_0(X8))
        | X10 != k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk1_4(X8,X9,X10,X11),k1_zfmisc_1(u1_struct_0(X8)))
        | r2_hidden(X11,X10)
        | ~ r2_hidden(X11,u1_struct_0(X8))
        | X10 != k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( v3_pre_topc(esk1_4(X8,X9,X10,X11),X8)
        | r2_hidden(X11,X10)
        | ~ r2_hidden(X11,u1_struct_0(X8))
        | X10 != k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(X11,esk1_4(X8,X9,X10,X11))
        | r2_hidden(X11,X10)
        | ~ r2_hidden(X11,u1_struct_0(X8))
        | X10 != k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( r1_xboole_0(X9,esk1_4(X8,X9,X10,X11))
        | r2_hidden(X11,X10)
        | ~ r2_hidden(X11,u1_struct_0(X8))
        | X10 != k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(esk2_3(X8,X9,X10),u1_struct_0(X8))
        | X10 = k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk3_3(X8,X9,X10),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ r2_hidden(esk2_3(X8,X9,X10),X10)
        | X10 = k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( v3_pre_topc(esk3_3(X8,X9,X10),X8)
        | ~ r2_hidden(esk2_3(X8,X9,X10),X10)
        | X10 = k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(esk2_3(X8,X9,X10),esk3_3(X8,X9,X10))
        | ~ r2_hidden(esk2_3(X8,X9,X10),X10)
        | X10 = k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( r1_xboole_0(X9,esk3_3(X8,X9,X10))
        | ~ r2_hidden(esk2_3(X8,X9,X10),X10)
        | X10 = k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(esk2_3(X8,X9,X10),X10)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_pre_topc(X16,X8)
        | ~ r2_hidden(esk2_3(X8,X9,X10),X16)
        | ~ r1_xboole_0(X9,X16)
        | X10 = k2_pre_topc(X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk6_0,X1)
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r1_xboole_0(X1,esk1_4(X2,X1,X3,X4))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X2))
    | X3 != k2_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | r2_hidden(X1,X2)
    | X2 != k2_pre_topc(X3,esk5_0)
    | ~ v3_pre_topc(esk1_4(X3,esk5_0,X2,X1),esk4_0)
    | ~ l1_pre_topc(X3)
    | ~ r2_hidden(esk6_0,esk1_4(X3,esk5_0,X2,X1))
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ m1_subset_1(esk1_4(X3,esk5_0,X2,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,plain,
    ( v3_pre_topc(esk1_4(X1,X2,X3,X4),X1)
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_15,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | m1_subset_1(k2_pre_topc(X17,X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | r2_hidden(X1,X2)
    | X2 != k2_pre_topc(esk4_0,esk5_0)
    | ~ r2_hidden(esk6_0,esk1_4(esk4_0,esk5_0,X2,X1))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk1_4(esk4_0,esk5_0,X2,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,esk1_4(X2,X3,X4,X1))
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | X4 != k2_pre_topc(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | r2_hidden(esk6_0,X1)
    | X1 != k2_pre_topc(esk4_0,esk5_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk1_4(esk4_0,esk5_0,X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_13]),c_0_14])])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v3_pre_topc(X3,X4)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X5,X3)
    | ~ r2_hidden(X1,u1_struct_0(X4))
    | X2 != k2_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | r2_hidden(esk6_0,X1)
    | X1 != k2_pre_topc(esk4_0,esk5_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13]),c_0_14])])).

cnf(c_0_24,negated_conjecture,
    ( k2_pre_topc(esk4_0,X1) != k2_pre_topc(esk4_0,X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ v3_pre_topc(X3,esk4_0)
    | ~ r2_hidden(X4,k2_pre_topc(esk4_0,X1))
    | ~ r2_hidden(X4,u1_struct_0(esk4_0))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_13])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) != k2_pre_topc(esk4_0,X1)
    | ~ r1_xboole_0(X1,X2)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) != k2_pre_topc(esk4_0,X1)
    | ~ r1_xboole_0(X1,X2)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_22]),c_0_14])])).

cnf(c_0_28,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0)
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) != k2_pre_topc(esk4_0,X1)
    | ~ r1_xboole_0(X1,esk7_0)
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk7_0)
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_33,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,X7)
      | v1_xboole_0(X7)
      | r2_hidden(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_14])])).

fof(c_0_35,plain,(
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_22]),c_0_14])])).

cnf(c_0_43,negated_conjecture,
    ( ~ l1_struct_0(esk4_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_45,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_46,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t39_tops_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_tops_1)).
% 0.14/0.38  fof(d13_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k2_pre_topc(X1,X2)<=>![X4]:(r2_hidden(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X5,X1)&r2_hidden(X4,X5))&r1_xboole_0(X2,X5)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_pre_topc)).
% 0.14/0.38  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.14/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4))))))))), inference(assume_negation,[status(cth)],[t39_tops_1])).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ![X25]:(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(((m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)))&(((v3_pre_topc(esk7_0,esk4_0)|~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)))&(r2_hidden(esk6_0,esk7_0)|~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))))&(r1_xboole_0(esk5_0,esk7_0)|~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)))))&(r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk4_0)))|(~v3_pre_topc(X25,esk4_0)|~r2_hidden(esk6_0,X25)|~r1_xboole_0(esk5_0,X25)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X8, X9, X10, X11, X12, X16]:(((~r2_hidden(X11,X10)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X8)))|(~v3_pre_topc(X12,X8)|~r2_hidden(X11,X12)|~r1_xboole_0(X9,X12)))|~r2_hidden(X11,u1_struct_0(X8))|X10!=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&((m1_subset_1(esk1_4(X8,X9,X10,X11),k1_zfmisc_1(u1_struct_0(X8)))|r2_hidden(X11,X10)|~r2_hidden(X11,u1_struct_0(X8))|X10!=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(((v3_pre_topc(esk1_4(X8,X9,X10,X11),X8)|r2_hidden(X11,X10)|~r2_hidden(X11,u1_struct_0(X8))|X10!=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(r2_hidden(X11,esk1_4(X8,X9,X10,X11))|r2_hidden(X11,X10)|~r2_hidden(X11,u1_struct_0(X8))|X10!=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8)))&(r1_xboole_0(X9,esk1_4(X8,X9,X10,X11))|r2_hidden(X11,X10)|~r2_hidden(X11,u1_struct_0(X8))|X10!=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8)))))&((r2_hidden(esk2_3(X8,X9,X10),u1_struct_0(X8))|X10=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(((m1_subset_1(esk3_3(X8,X9,X10),k1_zfmisc_1(u1_struct_0(X8)))|~r2_hidden(esk2_3(X8,X9,X10),X10)|X10=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(((v3_pre_topc(esk3_3(X8,X9,X10),X8)|~r2_hidden(esk2_3(X8,X9,X10),X10)|X10=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(r2_hidden(esk2_3(X8,X9,X10),esk3_3(X8,X9,X10))|~r2_hidden(esk2_3(X8,X9,X10),X10)|X10=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8)))&(r1_xboole_0(X9,esk3_3(X8,X9,X10))|~r2_hidden(esk2_3(X8,X9,X10),X10)|X10=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))))&(r2_hidden(esk2_3(X8,X9,X10),X10)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X8)))|(~v3_pre_topc(X16,X8)|~r2_hidden(esk2_3(X8,X9,X10),X16)|~r1_xboole_0(X9,X16)))|X10=k2_pre_topc(X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).
% 0.14/0.38  cnf(c_0_9, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_pre_topc(X1,esk4_0)|~r2_hidden(esk6_0,X1)|~r1_xboole_0(esk5_0,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_10, plain, (r1_xboole_0(X1,esk1_4(X2,X1,X3,X4))|r2_hidden(X4,X3)|~r2_hidden(X4,u1_struct_0(X2))|X3!=k2_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))|r2_hidden(X1,X2)|X2!=k2_pre_topc(X3,esk5_0)|~v3_pre_topc(esk1_4(X3,esk5_0,X2,X1),esk4_0)|~l1_pre_topc(X3)|~r2_hidden(esk6_0,esk1_4(X3,esk5_0,X2,X1))|~r2_hidden(X1,u1_struct_0(X3))|~m1_subset_1(esk1_4(X3,esk5_0,X2,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.38  cnf(c_0_12, plain, (v3_pre_topc(esk1_4(X1,X2,X3,X4),X1)|r2_hidden(X4,X3)|~r2_hidden(X4,u1_struct_0(X1))|X3!=k2_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  fof(c_0_15, plain, ![X17, X18]:(~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|m1_subset_1(k2_pre_topc(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))|r2_hidden(X1,X2)|X2!=k2_pre_topc(esk4_0,esk5_0)|~r2_hidden(esk6_0,esk1_4(esk4_0,esk5_0,X2,X1))|~r2_hidden(X1,u1_struct_0(esk4_0))|~m1_subset_1(esk1_4(esk4_0,esk5_0,X2,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14])])).
% 0.14/0.38  cnf(c_0_17, plain, (r2_hidden(X1,esk1_4(X2,X3,X4,X1))|r2_hidden(X1,X4)|~r2_hidden(X1,u1_struct_0(X2))|X4!=k2_pre_topc(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_18, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))|r2_hidden(esk6_0,X1)|X1!=k2_pre_topc(esk4_0,esk5_0)|~r2_hidden(esk6_0,u1_struct_0(esk4_0))|~m1_subset_1(esk1_4(esk4_0,esk5_0,X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_13]), c_0_14])])).
% 0.14/0.38  cnf(c_0_20, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X1)))|r2_hidden(X4,X3)|~r2_hidden(X4,u1_struct_0(X1))|X3!=k2_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~v3_pre_topc(X3,X4)|~r2_hidden(X1,X3)|~r1_xboole_0(X5,X3)|~r2_hidden(X1,u1_struct_0(X4))|X2!=k2_pre_topc(X4,X5)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))|r2_hidden(esk6_0,X1)|X1!=k2_pre_topc(esk4_0,esk5_0)|~r2_hidden(esk6_0,u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_13]), c_0_14])])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (k2_pre_topc(esk4_0,X1)!=k2_pre_topc(esk4_0,X2)|~r1_xboole_0(X2,X3)|~v3_pre_topc(X3,esk4_0)|~r2_hidden(X4,k2_pre_topc(esk4_0,X1))|~r2_hidden(X4,u1_struct_0(esk4_0))|~r2_hidden(X4,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_13])])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))|~r2_hidden(esk6_0,u1_struct_0(esk4_0))|~m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(er,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (k2_pre_topc(esk4_0,esk5_0)!=k2_pre_topc(esk4_0,X1)|~r1_xboole_0(X1,X2)|~v3_pre_topc(X2,esk4_0)|~r2_hidden(esk6_0,u1_struct_0(esk4_0))|~r2_hidden(esk6_0,X2)|~m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_14])])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (k2_pre_topc(esk4_0,esk5_0)!=k2_pre_topc(esk4_0,X1)|~r1_xboole_0(X1,X2)|~v3_pre_topc(X2,esk4_0)|~r2_hidden(esk6_0,u1_struct_0(esk4_0))|~r2_hidden(esk6_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_22]), c_0_14])])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)|~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk6_0,esk7_0)|~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (k2_pre_topc(esk4_0,esk5_0)!=k2_pre_topc(esk4_0,X1)|~r1_xboole_0(X1,esk7_0)|~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))|~r2_hidden(esk6_0,u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (r1_xboole_0(esk5_0,esk7_0)|~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  fof(c_0_33, plain, ![X6, X7]:(~m1_subset_1(X6,X7)|(v1_xboole_0(X7)|r2_hidden(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (~r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))|~r2_hidden(esk6_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_14])])).
% 0.14/0.38  fof(c_0_35, plain, ![X20]:(v2_struct_0(X20)|~l1_struct_0(X20)|~v1_xboole_0(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.38  cnf(c_0_36, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk6_0,u1_struct_0(esk4_0))|~m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_40, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk6_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_22]), c_0_14])])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (~l1_struct_0(esk4_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.38  fof(c_0_45, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.14/0.38  cnf(c_0_47, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_13])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 49
% 0.14/0.38  # Proof object clause steps            : 36
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 30
% 0.14/0.38  # Proof object clause conjectures      : 27
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 18
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 16
% 0.14/0.38  # Proof object simplifying inferences  : 26
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 6
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 25
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 25
% 0.14/0.38  # Processed clauses                    : 103
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 103
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 4
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 73
% 0.14/0.38  # ...of the previous two non-trivial   : 71
% 0.14/0.38  # Contextual simplify-reflections      : 8
% 0.14/0.38  # Paramodulations                      : 70
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 72
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 64
% 0.14/0.38  # Current number of unprocessed clauses: 18
% 0.14/0.38  # ...number of literals in the above   : 127
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 31
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 2196
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 280
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.14/0.38  # Unit Clause-clause subsumption calls : 63
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 6489
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.043 s
% 0.14/0.38  # System time              : 0.000 s
% 0.14/0.38  # Total time               : 0.043 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
