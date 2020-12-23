%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 461 expanded)
%              Number of clauses        :   53 ( 188 expanded)
%              Number of leaves         :   12 ( 114 expanded)
%              Depth                    :   20
%              Number of atoms          :  302 (2849 expanded)
%              Number of equality atoms :   26 (  68 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X28,X29,X30,X32,X34] :
      ( ( r1_tarski(k2_struct_0(X29),k2_struct_0(X28))
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk3_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))
        | ~ r2_hidden(X30,u1_pre_topc(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( r2_hidden(esk3_3(X28,X29,X30),u1_pre_topc(X28))
        | ~ r2_hidden(X30,u1_pre_topc(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( X30 = k9_subset_1(u1_struct_0(X29),esk3_3(X28,X29,X30),k2_struct_0(X29))
        | ~ r2_hidden(X30,u1_pre_topc(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ r2_hidden(X32,u1_pre_topc(X28))
        | X30 != k9_subset_1(u1_struct_0(X29),X32,k2_struct_0(X29))
        | r2_hidden(X30,u1_pre_topc(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk4_2(X28,X29),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ r1_tarski(k2_struct_0(X29),k2_struct_0(X28))
        | m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( ~ r2_hidden(esk4_2(X28,X29),u1_pre_topc(X29))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ r2_hidden(X34,u1_pre_topc(X28))
        | esk4_2(X28,X29) != k9_subset_1(u1_struct_0(X29),X34,k2_struct_0(X29))
        | ~ r1_tarski(k2_struct_0(X29),k2_struct_0(X28))
        | m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk5_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))
        | r2_hidden(esk4_2(X28,X29),u1_pre_topc(X29))
        | ~ r1_tarski(k2_struct_0(X29),k2_struct_0(X28))
        | m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( r2_hidden(esk5_2(X28,X29),u1_pre_topc(X28))
        | r2_hidden(esk4_2(X28,X29),u1_pre_topc(X29))
        | ~ r1_tarski(k2_struct_0(X29),k2_struct_0(X28))
        | m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( esk4_2(X28,X29) = k9_subset_1(u1_struct_0(X29),esk5_2(X28,X29),k2_struct_0(X29))
        | r2_hidden(esk4_2(X28,X29),u1_pre_topc(X29))
        | ~ r1_tarski(k2_struct_0(X29),k2_struct_0(X28))
        | m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_14,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | l1_pre_topc(X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_15,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_16,plain,(
    ! [X41,X42] :
      ( ~ l1_struct_0(X41)
      | ~ l1_struct_0(X42)
      | ~ r1_tsep_1(X41,X42)
      | r1_tsep_1(X42,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tsep_1(esk8_0,esk9_0)
    | r1_tsep_1(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X36] :
      ( ~ l1_pre_topc(X36)
      | l1_struct_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk9_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | ~ r1_tarski(X26,X25)
      | r1_tarski(k2_xboole_0(X24,X26),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

fof(c_0_29,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tsep_1(esk9_0,esk8_0)
    | ~ l1_struct_0(esk9_0)
    | ~ l1_struct_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_24]),c_0_20])])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk7_0),k2_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X39,X40] :
      ( ( ~ r1_tsep_1(X39,X40)
        | r1_xboole_0(u1_struct_0(X39),u1_struct_0(X40))
        | ~ l1_struct_0(X40)
        | ~ l1_struct_0(X39) )
      & ( ~ r1_xboole_0(u1_struct_0(X39),u1_struct_0(X40))
        | r1_tsep_1(X39,X40)
        | ~ l1_struct_0(X40)
        | ~ l1_struct_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tsep_1(esk9_0,esk8_0)
    | ~ l1_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k2_struct_0(esk7_0)),k2_struct_0(esk8_0))
    | ~ r1_tarski(X1,k2_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X22,X23] : r1_tarski(X22,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_41,plain,(
    ! [X27] :
      ( ~ l1_struct_0(X27)
      | k2_struct_0(X27) = u1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_42,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r1_tsep_1(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_28])])).

fof(c_0_44,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_struct_0(esk8_0),k2_struct_0(esk7_0)),k2_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))
    | ~ l1_struct_0(esk8_0)
    | ~ l1_struct_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(k2_struct_0(esk8_0),k2_struct_0(esk7_0)) = k2_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_54,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_49]),c_0_20])])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_28])])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(k2_struct_0(esk8_0),u1_struct_0(esk7_0)) = k2_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_32])])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk8_0),u1_struct_0(esk7_0)) = u1_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_54]),c_0_28])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk7_0))
    | r2_hidden(esk2_2(X1,u1_struct_0(esk7_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(esk2_2(X1,u1_struct_0(esk7_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_67,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( r1_tsep_1(esk9_0,esk7_0)
    | ~ l1_struct_0(esk7_0)
    | ~ l1_struct_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( r1_tsep_1(esk9_0,esk7_0)
    | ~ l1_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_31]),c_0_55])])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tsep_1(esk7_0,esk9_0)
    | ~ r1_tsep_1(esk9_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( r1_tsep_1(esk9_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_31]),c_0_32])])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tsep_1(esk7_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_75,negated_conjecture,
    ( ~ l1_struct_0(esk7_0)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_73]),c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( ~ l1_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_31]),c_0_55])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_31]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.20/0.43  # and selection function SelectNewComplexAHPNS.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.029 s
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t23_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 0.20/0.43  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.20/0.43  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.43  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.20/0.43  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.43  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.20/0.43  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.43  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.43  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.43  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.43  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t23_tmap_1])).
% 0.20/0.43  fof(c_0_13, plain, ![X28, X29, X30, X32, X34]:(((r1_tarski(k2_struct_0(X29),k2_struct_0(X28))|~m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28))&((((m1_subset_1(esk3_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))|~r2_hidden(X30,u1_pre_topc(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|~m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28))&(r2_hidden(esk3_3(X28,X29,X30),u1_pre_topc(X28))|~r2_hidden(X30,u1_pre_topc(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|~m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28)))&(X30=k9_subset_1(u1_struct_0(X29),esk3_3(X28,X29,X30),k2_struct_0(X29))|~r2_hidden(X30,u1_pre_topc(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|~m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28)))&(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X28)))|~r2_hidden(X32,u1_pre_topc(X28))|X30!=k9_subset_1(u1_struct_0(X29),X32,k2_struct_0(X29))|r2_hidden(X30,u1_pre_topc(X29))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|~m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28))))&((m1_subset_1(esk4_2(X28,X29),k1_zfmisc_1(u1_struct_0(X29)))|~r1_tarski(k2_struct_0(X29),k2_struct_0(X28))|m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28))&((~r2_hidden(esk4_2(X28,X29),u1_pre_topc(X29))|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X28)))|~r2_hidden(X34,u1_pre_topc(X28))|esk4_2(X28,X29)!=k9_subset_1(u1_struct_0(X29),X34,k2_struct_0(X29)))|~r1_tarski(k2_struct_0(X29),k2_struct_0(X28))|m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28))&(((m1_subset_1(esk5_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))|r2_hidden(esk4_2(X28,X29),u1_pre_topc(X29))|~r1_tarski(k2_struct_0(X29),k2_struct_0(X28))|m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28))&(r2_hidden(esk5_2(X28,X29),u1_pre_topc(X28))|r2_hidden(esk4_2(X28,X29),u1_pre_topc(X29))|~r1_tarski(k2_struct_0(X29),k2_struct_0(X28))|m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28)))&(esk4_2(X28,X29)=k9_subset_1(u1_struct_0(X29),esk5_2(X28,X29),k2_struct_0(X29))|r2_hidden(esk4_2(X28,X29),u1_pre_topc(X29))|~r1_tarski(k2_struct_0(X29),k2_struct_0(X28))|m1_pre_topc(X29,X28)|~l1_pre_topc(X29)|~l1_pre_topc(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.20/0.43  fof(c_0_14, plain, ![X37, X38]:(~l1_pre_topc(X37)|(~m1_pre_topc(X38,X37)|l1_pre_topc(X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.43  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk6_0))&((~v2_struct_0(esk8_0)&m1_pre_topc(esk8_0,esk6_0))&((~v2_struct_0(esk9_0)&m1_pre_topc(esk9_0,esk6_0))&(m1_pre_topc(esk7_0,esk8_0)&((~r1_tsep_1(esk7_0,esk9_0)|~r1_tsep_1(esk9_0,esk7_0))&(r1_tsep_1(esk8_0,esk9_0)|r1_tsep_1(esk9_0,esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.20/0.43  fof(c_0_16, plain, ![X41, X42]:(~l1_struct_0(X41)|~l1_struct_0(X42)|(~r1_tsep_1(X41,X42)|r1_tsep_1(X42,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.20/0.43  cnf(c_0_17, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_18, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_19, negated_conjecture, (m1_pre_topc(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_21, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_22, negated_conjecture, (r1_tsep_1(esk8_0,esk9_0)|r1_tsep_1(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  fof(c_0_23, plain, ![X36]:(~l1_pre_topc(X36)|l1_struct_0(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.43  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk9_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  fof(c_0_25, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|~r1_tarski(X26,X25)|r1_tarski(k2_xboole_0(X24,X26),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.20/0.43  cnf(c_0_26, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.43  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.20/0.43  fof(c_0_29, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.43  cnf(c_0_30, negated_conjecture, (r1_tsep_1(esk9_0,esk8_0)|~l1_struct_0(esk9_0)|~l1_struct_0(esk8_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.43  cnf(c_0_31, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_24]), c_0_20])])).
% 0.20/0.43  cnf(c_0_33, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_34, negated_conjecture, (r1_tarski(k2_struct_0(esk7_0),k2_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.20/0.43  cnf(c_0_35, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  fof(c_0_36, plain, ![X39, X40]:((~r1_tsep_1(X39,X40)|r1_xboole_0(u1_struct_0(X39),u1_struct_0(X40))|~l1_struct_0(X40)|~l1_struct_0(X39))&(~r1_xboole_0(u1_struct_0(X39),u1_struct_0(X40))|r1_tsep_1(X39,X40)|~l1_struct_0(X40)|~l1_struct_0(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (r1_tsep_1(esk9_0,esk8_0)|~l1_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.20/0.43  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k2_struct_0(esk7_0)),k2_struct_0(esk8_0))|~r1_tarski(X1,k2_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.43  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_35])).
% 0.20/0.43  fof(c_0_40, plain, ![X22, X23]:r1_tarski(X22,k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.43  fof(c_0_41, plain, ![X27]:(~l1_struct_0(X27)|k2_struct_0(X27)=u1_struct_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.43  cnf(c_0_42, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (r1_tsep_1(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_28])])).
% 0.20/0.43  fof(c_0_44, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.43  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (r1_tarski(k2_xboole_0(k2_struct_0(esk8_0),k2_struct_0(esk7_0)),k2_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.43  cnf(c_0_47, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.43  cnf(c_0_48, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))|~l1_struct_0(esk8_0)|~l1_struct_0(esk9_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.43  cnf(c_0_51, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.43  fof(c_0_52, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (k2_xboole_0(k2_struct_0(esk8_0),k2_struct_0(esk7_0))=k2_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.20/0.43  cnf(c_0_54, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_49]), c_0_20])])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))|~l1_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_28])])).
% 0.20/0.43  cnf(c_0_57, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.43  cnf(c_0_58, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (k2_xboole_0(k2_struct_0(esk8_0),u1_struct_0(esk7_0))=k2_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.20/0.43  cnf(c_0_60, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_32])])).
% 0.20/0.43  cnf(c_0_62, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.43  cnf(c_0_63, negated_conjecture, (k2_xboole_0(u1_struct_0(esk8_0),u1_struct_0(esk7_0))=u1_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_54]), c_0_28])])).
% 0.20/0.43  cnf(c_0_64, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk8_0))|~r2_hidden(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.43  cnf(c_0_65, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk7_0))|r2_hidden(esk2_2(X1,u1_struct_0(esk7_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk7_0))|~r2_hidden(esk2_2(X1,u1_struct_0(esk7_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.43  cnf(c_0_67, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.43  cnf(c_0_68, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.43  cnf(c_0_69, negated_conjecture, (r1_xboole_0(u1_struct_0(esk9_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.43  cnf(c_0_70, negated_conjecture, (r1_tsep_1(esk9_0,esk7_0)|~l1_struct_0(esk7_0)|~l1_struct_0(esk9_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.43  cnf(c_0_71, negated_conjecture, (r1_tsep_1(esk9_0,esk7_0)|~l1_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_31]), c_0_55])])).
% 0.20/0.43  cnf(c_0_72, negated_conjecture, (~r1_tsep_1(esk7_0,esk9_0)|~r1_tsep_1(esk9_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_73, negated_conjecture, (r1_tsep_1(esk9_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_31]), c_0_32])])).
% 0.20/0.43  cnf(c_0_74, negated_conjecture, (~r1_tsep_1(esk7_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, (~l1_struct_0(esk7_0)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_73]), c_0_74])).
% 0.20/0.43  cnf(c_0_76, negated_conjecture, (~l1_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_31]), c_0_55])])).
% 0.20/0.43  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_31]), c_0_32])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 78
% 0.20/0.43  # Proof object clause steps            : 53
% 0.20/0.43  # Proof object formula steps           : 25
% 0.20/0.43  # Proof object conjectures             : 36
% 0.20/0.43  # Proof object clause conjectures      : 33
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 22
% 0.20/0.43  # Proof object initial formulas used   : 12
% 0.20/0.43  # Proof object generating inferences   : 27
% 0.20/0.43  # Proof object simplifying inferences  : 36
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 12
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 42
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 42
% 0.20/0.43  # Processed clauses                    : 619
% 0.20/0.43  # ...of these trivial                  : 21
% 0.20/0.43  # ...subsumed                          : 192
% 0.20/0.43  # ...remaining for further processing  : 406
% 0.20/0.43  # Other redundant clauses eliminated   : 6
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 5
% 0.20/0.43  # Backward-rewritten                   : 12
% 0.20/0.43  # Generated clauses                    : 4205
% 0.20/0.43  # ...of the previous two non-trivial   : 3877
% 0.20/0.43  # Contextual simplify-reflections      : 5
% 0.20/0.43  # Paramodulations                      : 4169
% 0.20/0.43  # Factorizations                       : 30
% 0.20/0.43  # Equation resolutions                 : 6
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 383
% 0.20/0.43  #    Positive orientable unit clauses  : 122
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 6
% 0.20/0.43  #    Non-unit-clauses                  : 255
% 0.20/0.43  # Current number of unprocessed clauses: 3276
% 0.20/0.43  # ...number of literals in the above   : 4337
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 17
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 7450
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 4434
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 202
% 0.20/0.43  # Unit Clause-clause subsumption calls : 384
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 291
% 0.20/0.43  # BW rewrite match successes           : 10
% 0.20/0.43  # Condensation attempts                : 619
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 73959
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.080 s
% 0.20/0.43  # System time              : 0.008 s
% 0.20/0.43  # Total time               : 0.088 s
% 0.20/0.43  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
