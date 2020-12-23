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
% DateTime   : Thu Dec  3 11:16:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 437 expanded)
%              Number of clauses        :   47 ( 176 expanded)
%              Number of leaves         :   10 ( 108 expanded)
%              Depth                    :   20
%              Number of atoms          :  277 (2779 expanded)
%              Number of equality atoms :   21 (  50 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( m1_pre_topc(X2,X3)
                   => ( ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X4,X2) )
                      | ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( m1_pre_topc(X2,X3)
                     => ( ( r1_tsep_1(X2,X4)
                          & r1_tsep_1(X4,X2) )
                        | ( ~ r1_tsep_1(X3,X4)
                          & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tmap_1])).

fof(c_0_11,plain,(
    ! [X36,X37] :
      ( ~ l1_struct_0(X36)
      | ~ l1_struct_0(X37)
      | ~ r1_tsep_1(X36,X37)
      | r1_tsep_1(X37,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk6_0)
    & ~ v2_struct_0(esk8_0)
    & m1_pre_topc(esk8_0,esk6_0)
    & ~ v2_struct_0(esk9_0)
    & m1_pre_topc(esk9_0,esk6_0)
    & m1_pre_topc(esk7_0,esk8_0)
    & ( ~ r1_tsep_1(esk7_0,esk9_0)
      | ~ r1_tsep_1(esk9_0,esk7_0) )
    & ( r1_tsep_1(esk8_0,esk9_0)
      | r1_tsep_1(esk9_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | l1_pre_topc(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_14,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r1_tsep_1(esk8_0,esk9_0)
    | r1_tsep_1(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_17,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk9_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X23,X24,X25,X27,X29] :
      ( ( r1_tarski(k2_struct_0(X24),k2_struct_0(X23))
        | ~ m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk3_3(X23,X24,X25),k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(X25,u1_pre_topc(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk3_3(X23,X24,X25),u1_pre_topc(X23))
        | ~ r2_hidden(X25,u1_pre_topc(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) )
      & ( X25 = k9_subset_1(u1_struct_0(X24),esk3_3(X23,X24,X25),k2_struct_0(X24))
        | ~ r2_hidden(X25,u1_pre_topc(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) )
      & ( ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(X27,u1_pre_topc(X23))
        | X25 != k9_subset_1(u1_struct_0(X24),X27,k2_struct_0(X24))
        | r2_hidden(X25,u1_pre_topc(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk4_2(X23,X24),k1_zfmisc_1(u1_struct_0(X24)))
        | ~ r1_tarski(k2_struct_0(X24),k2_struct_0(X23))
        | m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) )
      & ( ~ r2_hidden(esk4_2(X23,X24),u1_pre_topc(X24))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(X29,u1_pre_topc(X23))
        | esk4_2(X23,X24) != k9_subset_1(u1_struct_0(X24),X29,k2_struct_0(X24))
        | ~ r1_tarski(k2_struct_0(X24),k2_struct_0(X23))
        | m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk5_2(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))
        | r2_hidden(esk4_2(X23,X24),u1_pre_topc(X24))
        | ~ r1_tarski(k2_struct_0(X24),k2_struct_0(X23))
        | m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk5_2(X23,X24),u1_pre_topc(X23))
        | r2_hidden(esk4_2(X23,X24),u1_pre_topc(X24))
        | ~ r1_tarski(k2_struct_0(X24),k2_struct_0(X23))
        | m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) )
      & ( esk4_2(X23,X24) = k9_subset_1(u1_struct_0(X24),esk5_2(X23,X24),k2_struct_0(X24))
        | r2_hidden(esk4_2(X23,X24),u1_pre_topc(X24))
        | ~ r1_tarski(k2_struct_0(X24),k2_struct_0(X23))
        | m1_pre_topc(X24,X23)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tsep_1(esk9_0,esk8_0)
    | ~ l1_struct_0(esk9_0)
    | ~ l1_struct_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X22] :
      ( ~ l1_struct_0(X22)
      | k2_struct_0(X22) = u1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_27,plain,(
    ! [X34,X35] :
      ( ( ~ r1_tsep_1(X34,X35)
        | r1_xboole_0(u1_struct_0(X34),u1_struct_0(X35))
        | ~ l1_struct_0(X35)
        | ~ l1_struct_0(X34) )
      & ( ~ r1_xboole_0(u1_struct_0(X34),u1_struct_0(X35))
        | r1_tsep_1(X34,X35)
        | ~ l1_struct_0(X35)
        | ~ l1_struct_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tsep_1(esk9_0,esk8_0)
    | ~ l1_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_24]),c_0_19])])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tsep_1(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_29])])).

fof(c_0_35,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_36,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk7_0),k2_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_29])])).

cnf(c_0_38,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))
    | ~ l1_struct_0(esk8_0)
    | ~ l1_struct_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk7_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_29])])).

fof(c_0_43,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_22]),c_0_29])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(k2_struct_0(esk7_0),u1_struct_0(esk8_0)) = k2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_22]),c_0_23])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,k2_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(k2_struct_0(esk7_0),X1)
    | r2_hidden(esk2_2(k2_struct_0(esk7_0),X1),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(k2_struct_0(esk7_0),X1)
    | ~ r2_hidden(esk2_2(k2_struct_0(esk7_0),X1),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(k2_struct_0(esk7_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_55]),c_0_19])])).

cnf(c_0_58,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_38]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk9_0)
    | ~ l1_struct_0(esk9_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk9_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_22]),c_0_23])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tsep_1(esk7_0,esk9_0)
    | ~ r1_tsep_1(esk9_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_22]),c_0_57])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tsep_1(esk9_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_65,negated_conjecture,
    ( ~ l1_struct_0(esk9_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_63]),c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_22]),c_0_23])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_22]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.38  # and selection function SelectNewComplexAHPNS.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t23_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 0.19/0.38  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.19/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.19/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.38  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.19/0.38  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t23_tmap_1])).
% 0.19/0.38  fof(c_0_11, plain, ![X36, X37]:(~l1_struct_0(X36)|~l1_struct_0(X37)|(~r1_tsep_1(X36,X37)|r1_tsep_1(X37,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.19/0.38  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk6_0))&((~v2_struct_0(esk8_0)&m1_pre_topc(esk8_0,esk6_0))&((~v2_struct_0(esk9_0)&m1_pre_topc(esk9_0,esk6_0))&(m1_pre_topc(esk7_0,esk8_0)&((~r1_tsep_1(esk7_0,esk9_0)|~r1_tsep_1(esk9_0,esk7_0))&(r1_tsep_1(esk8_0,esk9_0)|r1_tsep_1(esk9_0,esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X32, X33]:(~l1_pre_topc(X32)|(~m1_pre_topc(X33,X32)|l1_pre_topc(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.38  cnf(c_0_14, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (r1_tsep_1(esk8_0,esk9_0)|r1_tsep_1(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_16, plain, ![X31]:(~l1_pre_topc(X31)|l1_struct_0(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  cnf(c_0_17, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk9_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_20, plain, ![X23, X24, X25, X27, X29]:(((r1_tarski(k2_struct_0(X24),k2_struct_0(X23))|~m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23))&((((m1_subset_1(esk3_3(X23,X24,X25),k1_zfmisc_1(u1_struct_0(X23)))|~r2_hidden(X25,u1_pre_topc(X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23))&(r2_hidden(esk3_3(X23,X24,X25),u1_pre_topc(X23))|~r2_hidden(X25,u1_pre_topc(X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23)))&(X25=k9_subset_1(u1_struct_0(X24),esk3_3(X23,X24,X25),k2_struct_0(X24))|~r2_hidden(X25,u1_pre_topc(X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23)))&(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X23)))|~r2_hidden(X27,u1_pre_topc(X23))|X25!=k9_subset_1(u1_struct_0(X24),X27,k2_struct_0(X24))|r2_hidden(X25,u1_pre_topc(X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23))))&((m1_subset_1(esk4_2(X23,X24),k1_zfmisc_1(u1_struct_0(X24)))|~r1_tarski(k2_struct_0(X24),k2_struct_0(X23))|m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23))&((~r2_hidden(esk4_2(X23,X24),u1_pre_topc(X24))|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X23)))|~r2_hidden(X29,u1_pre_topc(X23))|esk4_2(X23,X24)!=k9_subset_1(u1_struct_0(X24),X29,k2_struct_0(X24)))|~r1_tarski(k2_struct_0(X24),k2_struct_0(X23))|m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23))&(((m1_subset_1(esk5_2(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))|r2_hidden(esk4_2(X23,X24),u1_pre_topc(X24))|~r1_tarski(k2_struct_0(X24),k2_struct_0(X23))|m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23))&(r2_hidden(esk5_2(X23,X24),u1_pre_topc(X23))|r2_hidden(esk4_2(X23,X24),u1_pre_topc(X24))|~r1_tarski(k2_struct_0(X24),k2_struct_0(X23))|m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23)))&(esk4_2(X23,X24)=k9_subset_1(u1_struct_0(X24),esk5_2(X23,X24),k2_struct_0(X24))|r2_hidden(esk4_2(X23,X24),u1_pre_topc(X24))|~r1_tarski(k2_struct_0(X24),k2_struct_0(X23))|m1_pre_topc(X24,X23)|~l1_pre_topc(X24)|~l1_pre_topc(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (r1_tsep_1(esk9_0,esk8_0)|~l1_struct_0(esk9_0)|~l1_struct_0(esk8_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_22, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_25, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  fof(c_0_26, plain, ![X22]:(~l1_struct_0(X22)|k2_struct_0(X22)=u1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.38  fof(c_0_27, plain, ![X34, X35]:((~r1_tsep_1(X34,X35)|r1_xboole_0(u1_struct_0(X34),u1_struct_0(X35))|~l1_struct_0(X35)|~l1_struct_0(X34))&(~r1_xboole_0(u1_struct_0(X34),u1_struct_0(X35))|r1_tsep_1(X34,X35)|~l1_struct_0(X35)|~l1_struct_0(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r1_tsep_1(esk9_0,esk8_0)|~l1_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_24]), c_0_19])])).
% 0.19/0.38  cnf(c_0_30, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_25, c_0_17])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_32, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_33, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (r1_tsep_1(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_22]), c_0_29])])).
% 0.19/0.38  fof(c_0_35, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.38  fof(c_0_36, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(k2_struct_0(esk7_0),k2_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_29])])).
% 0.19/0.38  cnf(c_0_38, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_32, c_0_22])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))|~l1_struct_0(esk8_0)|~l1_struct_0(esk9_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_struct_0(esk7_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_29])])).
% 0.19/0.38  fof(c_0_43, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))|~l1_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_22]), c_0_29])])).
% 0.19/0.38  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (k3_xboole_0(k2_struct_0(esk7_0),u1_struct_0(esk8_0))=k2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_47, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_22]), c_0_23])])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk8_0))|~r2_hidden(X1,k2_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.38  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk8_0))|~r2_hidden(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (r1_xboole_0(k2_struct_0(esk7_0),X1)|r2_hidden(esk2_2(k2_struct_0(esk7_0),X1),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r1_xboole_0(k2_struct_0(esk7_0),X1)|~r2_hidden(esk2_2(k2_struct_0(esk7_0),X1),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.38  cnf(c_0_54, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (m1_pre_topc(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (r1_xboole_0(k2_struct_0(esk7_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_55]), c_0_19])])).
% 0.19/0.38  cnf(c_0_58, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_38]), c_0_57])])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (r1_tsep_1(esk7_0,esk9_0)|~l1_struct_0(esk9_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (r1_tsep_1(esk7_0,esk9_0)|~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_22]), c_0_23])])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (~r1_tsep_1(esk7_0,esk9_0)|~r1_tsep_1(esk9_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (r1_tsep_1(esk7_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_22]), c_0_57])])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (~r1_tsep_1(esk9_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (~l1_struct_0(esk9_0)|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_63]), c_0_64])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_22]), c_0_23])])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_22]), c_0_57])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 68
% 0.19/0.38  # Proof object clause steps            : 47
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 35
% 0.19/0.38  # Proof object clause conjectures      : 32
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 19
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 25
% 0.19/0.38  # Proof object simplifying inferences  : 33
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 38
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 38
% 0.19/0.38  # Processed clauses                    : 164
% 0.19/0.38  # ...of these trivial                  : 21
% 0.19/0.38  # ...subsumed                          : 10
% 0.19/0.38  # ...remaining for further processing  : 133
% 0.19/0.38  # Other redundant clauses eliminated   : 4
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 5
% 0.19/0.38  # Backward-rewritten                   : 7
% 0.19/0.38  # Generated clauses                    : 365
% 0.19/0.38  # ...of the previous two non-trivial   : 325
% 0.19/0.38  # Contextual simplify-reflections      : 5
% 0.19/0.38  # Paramodulations                      : 357
% 0.19/0.38  # Factorizations                       : 4
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
% 0.19/0.38  # Current number of processed clauses  : 117
% 0.19/0.38  #    Positive orientable unit clauses  : 48
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 6
% 0.19/0.38  #    Non-unit-clauses                  : 63
% 0.19/0.38  # Current number of unprocessed clauses: 198
% 0.19/0.38  # ...number of literals in the above   : 632
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 12
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 865
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 317
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 20
% 0.19/0.38  # Unit Clause-clause subsumption calls : 13
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 5
% 0.19/0.38  # BW rewrite match successes           : 5
% 0.19/0.38  # Condensation attempts                : 164
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 8381
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.036 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
