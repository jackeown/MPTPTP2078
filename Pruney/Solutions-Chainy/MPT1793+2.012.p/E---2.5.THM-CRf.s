%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:19 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 307 expanded)
%              Number of clauses        :   61 ( 108 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  410 (1881 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t109_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(rc4_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(t64_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( ( X5 = X6
                              & r1_tmap_1(X2,X1,X3,X5) )
                           => r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t108_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ~ r2_hidden(X3,X2)
               => r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r1_xboole_0(u1_struct_0(X3),X2)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X3))
                     => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t109_tmap_1])).

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ( r1_tarski(X26,X27)
        | X26 != X27 )
      & ( r1_tarski(X27,X26)
        | X26 != X27 )
      & ( ~ r1_tarski(X26,X27)
        | ~ r1_tarski(X27,X26)
        | X26 = X27 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X32,k1_zfmisc_1(X33))
        | r1_tarski(X32,X33) )
      & ( ~ r1_tarski(X32,X33)
        | m1_subset_1(X32,k1_zfmisc_1(X33)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_20,plain,(
    ! [X37] :
      ( ( m1_subset_1(esk4_1(X37),k1_zfmisc_1(u1_struct_0(X37)))
        | v2_struct_0(X37)
        | ~ l1_struct_0(X37) )
      & ( ~ v1_xboole_0(esk4_1(X37))
        | v2_struct_0(X37)
        | ~ l1_struct_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_struct_0])])])])])).

fof(c_0_21,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | l1_pre_topc(X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk5_0)
    & r1_xboole_0(u1_struct_0(esk7_0),esk6_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & ~ r1_tmap_1(esk7_0,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_24,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_25,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_26,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_1(esk7_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk7_0),X1)
    | r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_48,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X20,X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk3_3(X22,X23,X24),X24)
        | ~ r2_hidden(esk3_3(X22,X23,X24),X22)
        | r2_hidden(esk3_3(X22,X23,X24),X23)
        | X24 = k4_xboole_0(X22,X23) )
      & ( r2_hidden(esk3_3(X22,X23,X24),X22)
        | r2_hidden(esk3_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk3_3(X22,X23,X24),X23)
        | r2_hidden(esk3_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_49,plain,(
    ! [X28,X29] :
      ( ( ~ r1_xboole_0(X28,X29)
        | k4_xboole_0(X28,X29) = X28 )
      & ( k4_xboole_0(X28,X29) != X28
        | r1_xboole_0(X28,X29) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_50,negated_conjecture,
    ( esk4_1(esk7_0) = u1_struct_0(esk7_0)
    | ~ m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(esk4_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(X1))
    | r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_52,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ l1_pre_topc(X39)
      | v2_struct_0(X40)
      | ~ m1_pre_topc(X40,X39)
      | ~ m1_subset_1(X41,u1_struct_0(X40))
      | m1_subset_1(X41,u1_struct_0(X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk4_1(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( esk4_1(esk7_0) = u1_struct_0(esk7_0)
    | r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_58,plain,(
    ! [X51,X52,X53,X54,X55,X56] :
      ( v2_struct_0(X51)
      | ~ v2_pre_topc(X51)
      | ~ l1_pre_topc(X51)
      | v2_struct_0(X52)
      | ~ v2_pre_topc(X52)
      | ~ l1_pre_topc(X52)
      | ~ v1_funct_1(X53)
      | ~ v1_funct_2(X53,u1_struct_0(X52),u1_struct_0(X51))
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X51))))
      | v2_struct_0(X54)
      | ~ m1_pre_topc(X54,X52)
      | ~ m1_subset_1(X55,u1_struct_0(X52))
      | ~ m1_subset_1(X56,u1_struct_0(X54))
      | X55 != X56
      | ~ r1_tmap_1(X52,X51,X53,X55)
      | r1_tmap_1(X54,X51,k2_tmap_1(X52,X51,X53,X54),X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

fof(c_0_59,plain,(
    ! [X44,X45] :
      ( ( v1_funct_1(k7_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))) )
      & ( v1_funct_2(k7_tmap_1(X44,X45),u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))) )
      & ( m1_subset_1(k7_tmap_1(X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

fof(c_0_60,plain,(
    ! [X42,X43] :
      ( ( v1_pre_topc(k6_tmap_1(X42,X43))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42))) )
      & ( v2_pre_topc(k6_tmap_1(X42,X43))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42))) )
      & ( l1_pre_topc(k6_tmap_1(X42,X43))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_61,plain,(
    ! [X48,X49,X50] :
      ( v2_struct_0(X48)
      | ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | ~ m1_subset_1(X50,u1_struct_0(X48))
      | r2_hidden(X50,X49)
      | r1_tmap_1(X48,k6_tmap_1(X48,X49),k7_tmap_1(X48,X49),X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t108_tmap_1])])])])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk7_0),esk6_0) = u1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_41]),c_0_43])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | X5 != X6
    | ~ r1_tmap_1(X2,X1,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_69,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_71,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_37]),c_0_41])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_30]),c_0_40])])).

cnf(c_0_79,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_62])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,esk6_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_33])]),c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_68]),c_0_69]),c_0_33])]),c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_68]),c_0_69]),c_0_33])]),c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_68]),c_0_69]),c_0_33])]),c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_68]),c_0_69]),c_0_33])]),c_0_70])).

cnf(c_0_85,negated_conjecture,
    ( r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1)
    | r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_68]),c_0_69]),c_0_33])]),c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_32]),c_0_33])]),c_0_70])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1),X2)
    | v2_struct_0(k6_tmap_1(esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_69]),c_0_83]),c_0_33]),c_0_84])]),c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

fof(c_0_90,plain,(
    ! [X46,X47] :
      ( ( ~ v2_struct_0(k6_tmap_1(X46,X47))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46))) )
      & ( v1_pre_topc(k6_tmap_1(X46,X47))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46))) )
      & ( v2_pre_topc(k6_tmap_1(X46,X47))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1),esk8_0)
    | v2_struct_0(k6_tmap_1(esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_93,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_37]),c_0_32])]),c_0_92]),c_0_41])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_69]),c_0_33]),c_0_68])]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.77  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.60/0.77  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.60/0.77  #
% 0.60/0.77  # Preprocessing time       : 0.040 s
% 0.60/0.77  
% 0.60/0.77  # Proof found!
% 0.60/0.77  # SZS status Theorem
% 0.60/0.77  # SZS output start CNFRefutation
% 0.60/0.77  fof(t109_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_xboole_0(u1_struct_0(X3),X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 0.60/0.77  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.60/0.77  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.60/0.77  fof(rc4_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_struct_0)).
% 0.60/0.77  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.60/0.77  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.60/0.77  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.60/0.77  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.60/0.77  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.60/0.77  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.60/0.77  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.60/0.77  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.60/0.77  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.60/0.77  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.60/0.77  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.60/0.77  fof(t108_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(~(r2_hidden(X3,X2))=>r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 0.60/0.77  fof(fc4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((~(v2_struct_0(k6_tmap_1(X1,X2)))&v1_pre_topc(k6_tmap_1(X1,X2)))&v2_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 0.60/0.77  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_xboole_0(u1_struct_0(X3),X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4))))))), inference(assume_negation,[status(cth)],[t109_tmap_1])).
% 0.60/0.77  fof(c_0_18, plain, ![X26, X27]:(((r1_tarski(X26,X27)|X26!=X27)&(r1_tarski(X27,X26)|X26!=X27))&(~r1_tarski(X26,X27)|~r1_tarski(X27,X26)|X26=X27)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.60/0.77  fof(c_0_19, plain, ![X32, X33]:((~m1_subset_1(X32,k1_zfmisc_1(X33))|r1_tarski(X32,X33))&(~r1_tarski(X32,X33)|m1_subset_1(X32,k1_zfmisc_1(X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.60/0.77  fof(c_0_20, plain, ![X37]:((m1_subset_1(esk4_1(X37),k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~l1_struct_0(X37)))&(~v1_xboole_0(esk4_1(X37))|(v2_struct_0(X37)|~l1_struct_0(X37)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_struct_0])])])])])).
% 0.60/0.77  fof(c_0_21, plain, ![X34]:(~l1_pre_topc(X34)|l1_struct_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.60/0.77  fof(c_0_22, plain, ![X35, X36]:(~l1_pre_topc(X35)|(~m1_pre_topc(X36,X35)|l1_pre_topc(X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.60/0.77  fof(c_0_23, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk5_0))&(r1_xboole_0(u1_struct_0(esk7_0),esk6_0)&(m1_subset_1(esk8_0,u1_struct_0(esk7_0))&~r1_tmap_1(esk7_0,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk7_0),esk8_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.60/0.77  fof(c_0_24, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.60/0.77  fof(c_0_25, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.60/0.77  fof(c_0_26, plain, ![X30, X31]:(~m1_subset_1(X30,X31)|(v1_xboole_0(X31)|r2_hidden(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.60/0.77  cnf(c_0_27, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.77  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.77  cnf(c_0_29, plain, (m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.60/0.77  cnf(c_0_30, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.77  cnf(c_0_31, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.77  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  cnf(c_0_34, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.77  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.60/0.77  cnf(c_0_36, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.60/0.77  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  cnf(c_0_38, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.60/0.77  cnf(c_0_39, plain, (v2_struct_0(X1)|m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.60/0.77  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.60/0.77  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.60/0.77  cnf(c_0_43, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk7_0))|v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.60/0.77  cnf(c_0_44, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_38, c_0_28])).
% 0.60/0.77  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk4_1(esk7_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.60/0.77  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.77  cnf(c_0_47, negated_conjecture, (r1_tarski(u1_struct_0(esk7_0),X1)|r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.60/0.77  fof(c_0_48, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:((((r2_hidden(X20,X17)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18)))&(~r2_hidden(X21,X17)|r2_hidden(X21,X18)|r2_hidden(X21,X19)|X19!=k4_xboole_0(X17,X18)))&((~r2_hidden(esk3_3(X22,X23,X24),X24)|(~r2_hidden(esk3_3(X22,X23,X24),X22)|r2_hidden(esk3_3(X22,X23,X24),X23))|X24=k4_xboole_0(X22,X23))&((r2_hidden(esk3_3(X22,X23,X24),X22)|r2_hidden(esk3_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))&(~r2_hidden(esk3_3(X22,X23,X24),X23)|r2_hidden(esk3_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.60/0.77  fof(c_0_49, plain, ![X28, X29]:((~r1_xboole_0(X28,X29)|k4_xboole_0(X28,X29)=X28)&(k4_xboole_0(X28,X29)!=X28|r1_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.60/0.77  cnf(c_0_50, negated_conjecture, (esk4_1(esk7_0)=u1_struct_0(esk7_0)|~m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(esk4_1(esk7_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.60/0.77  cnf(c_0_51, negated_conjecture, (m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(X1))|r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.60/0.77  fof(c_0_52, plain, ![X39, X40, X41]:(v2_struct_0(X39)|~l1_pre_topc(X39)|(v2_struct_0(X40)|~m1_pre_topc(X40,X39)|(~m1_subset_1(X41,u1_struct_0(X40))|m1_subset_1(X41,u1_struct_0(X39))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.60/0.77  cnf(c_0_53, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.60/0.77  cnf(c_0_54, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.60/0.77  cnf(c_0_55, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  cnf(c_0_56, plain, (v2_struct_0(X1)|~v1_xboole_0(esk4_1(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.60/0.77  cnf(c_0_57, negated_conjecture, (esk4_1(esk7_0)=u1_struct_0(esk7_0)|r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.60/0.77  fof(c_0_58, plain, ![X51, X52, X53, X54, X55, X56]:(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52)|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X52),u1_struct_0(X51))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X51))))|(v2_struct_0(X54)|~m1_pre_topc(X54,X52)|(~m1_subset_1(X55,u1_struct_0(X52))|(~m1_subset_1(X56,u1_struct_0(X54))|(X55!=X56|~r1_tmap_1(X52,X51,X53,X55)|r1_tmap_1(X54,X51,k2_tmap_1(X52,X51,X53,X54),X56)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.60/0.77  fof(c_0_59, plain, ![X44, X45]:(((v1_funct_1(k7_tmap_1(X44,X45))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))))&(v1_funct_2(k7_tmap_1(X44,X45),u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))))))&(m1_subset_1(k7_tmap_1(X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(k6_tmap_1(X44,X45)))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.60/0.77  fof(c_0_60, plain, ![X42, X43]:(((v1_pre_topc(k6_tmap_1(X42,X43))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))))&(v2_pre_topc(k6_tmap_1(X42,X43))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42))))))&(l1_pre_topc(k6_tmap_1(X42,X43))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.60/0.77  fof(c_0_61, plain, ![X48, X49, X50]:(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|(~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|(~m1_subset_1(X50,u1_struct_0(X48))|(r2_hidden(X50,X49)|r1_tmap_1(X48,k6_tmap_1(X48,X49),k7_tmap_1(X48,X49),X50))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t108_tmap_1])])])])).
% 0.60/0.77  cnf(c_0_62, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.60/0.77  cnf(c_0_63, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_53])).
% 0.60/0.77  cnf(c_0_64, negated_conjecture, (k4_xboole_0(u1_struct_0(esk7_0),esk6_0)=u1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.60/0.77  cnf(c_0_65, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk7_0))|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_41]), c_0_43])).
% 0.60/0.77  cnf(c_0_66, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.60/0.77  cnf(c_0_67, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.60/0.77  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  cnf(c_0_69, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  cnf(c_0_70, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  cnf(c_0_71, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.60/0.77  cnf(c_0_72, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.60/0.77  cnf(c_0_73, plain, (v2_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.60/0.77  cnf(c_0_74, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.60/0.77  cnf(c_0_75, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.60/0.77  cnf(c_0_76, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(esk8_0,u1_struct_0(X1))|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_37]), c_0_41])).
% 0.60/0.77  cnf(c_0_77, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk7_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.60/0.77  cnf(c_0_78, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_30]), c_0_40])])).
% 0.60/0.77  cnf(c_0_79, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]), c_0_62])).
% 0.60/0.77  cnf(c_0_80, negated_conjecture, (m1_subset_1(k7_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,esk6_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_33])]), c_0_70])).
% 0.60/0.77  cnf(c_0_81, negated_conjecture, (v1_funct_2(k7_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_68]), c_0_69]), c_0_33])]), c_0_70])).
% 0.60/0.77  cnf(c_0_82, negated_conjecture, (v1_funct_1(k7_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_68]), c_0_69]), c_0_33])]), c_0_70])).
% 0.60/0.77  cnf(c_0_83, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_68]), c_0_69]), c_0_33])]), c_0_70])).
% 0.60/0.77  cnf(c_0_84, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_68]), c_0_69]), c_0_33])]), c_0_70])).
% 0.60/0.77  cnf(c_0_85, negated_conjecture, (r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1)|r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_68]), c_0_69]), c_0_33])]), c_0_70])).
% 0.60/0.77  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_32]), c_0_33])]), c_0_70])).
% 0.60/0.77  cnf(c_0_87, negated_conjecture, (~r2_hidden(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.60/0.77  cnf(c_0_88, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1),X2)|v2_struct_0(k6_tmap_1(esk5_0,esk6_0))|v2_struct_0(X1)|~r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X2)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_82]), c_0_69]), c_0_83]), c_0_33]), c_0_84])]), c_0_70])).
% 0.60/0.77  cnf(c_0_89, negated_conjecture, (r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.60/0.77  fof(c_0_90, plain, ![X46, X47]:(((~v2_struct_0(k6_tmap_1(X46,X47))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))))&(v1_pre_topc(k6_tmap_1(X46,X47))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46))))))&(v2_pre_topc(k6_tmap_1(X46,X47))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).
% 0.60/0.77  cnf(c_0_91, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1),esk8_0)|v2_struct_0(k6_tmap_1(esk5_0,esk6_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.60/0.77  cnf(c_0_92, negated_conjecture, (~r1_tmap_1(esk7_0,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  cnf(c_0_93, plain, (v2_struct_0(X1)|~v2_struct_0(k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.60/0.77  cnf(c_0_94, negated_conjecture, (v2_struct_0(k6_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_37]), c_0_32])]), c_0_92]), c_0_41])).
% 0.60/0.77  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_69]), c_0_33]), c_0_68])]), c_0_70]), ['proof']).
% 0.60/0.77  # SZS output end CNFRefutation
% 0.60/0.77  # Proof object total steps             : 96
% 0.60/0.77  # Proof object clause steps            : 61
% 0.60/0.77  # Proof object formula steps           : 35
% 0.60/0.77  # Proof object conjectures             : 37
% 0.60/0.77  # Proof object clause conjectures      : 34
% 0.60/0.77  # Proof object formula conjectures     : 3
% 0.60/0.77  # Proof object initial clauses used    : 30
% 0.60/0.77  # Proof object initial formulas used   : 17
% 0.60/0.77  # Proof object generating inferences   : 30
% 0.60/0.77  # Proof object simplifying inferences  : 55
% 0.60/0.77  # Training examples: 0 positive, 0 negative
% 0.60/0.77  # Parsed axioms                        : 17
% 0.60/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.77  # Initial clauses                      : 44
% 0.60/0.77  # Removed in clause preprocessing      : 0
% 0.60/0.77  # Initial clauses in saturation        : 44
% 0.60/0.77  # Processed clauses                    : 2298
% 0.60/0.77  # ...of these trivial                  : 29
% 0.60/0.77  # ...subsumed                          : 1392
% 0.60/0.77  # ...remaining for further processing  : 877
% 0.60/0.77  # Other redundant clauses eliminated   : 6
% 0.60/0.77  # Clauses deleted for lack of memory   : 0
% 0.60/0.77  # Backward-subsumed                    : 20
% 0.60/0.77  # Backward-rewritten                   : 54
% 0.60/0.77  # Generated clauses                    : 19776
% 0.60/0.77  # ...of the previous two non-trivial   : 19085
% 0.60/0.77  # Contextual simplify-reflections      : 51
% 0.60/0.77  # Paramodulations                      : 19543
% 0.60/0.77  # Factorizations                       : 222
% 0.60/0.77  # Equation resolutions                 : 11
% 0.60/0.77  # Propositional unsat checks           : 0
% 0.60/0.77  #    Propositional check models        : 0
% 0.60/0.77  #    Propositional check unsatisfiable : 0
% 0.60/0.77  #    Propositional clauses             : 0
% 0.60/0.77  #    Propositional clauses after purity: 0
% 0.60/0.77  #    Propositional unsat core size     : 0
% 0.60/0.77  #    Propositional preprocessing time  : 0.000
% 0.60/0.77  #    Propositional encoding time       : 0.000
% 0.60/0.77  #    Propositional solver time         : 0.000
% 0.60/0.77  #    Success case prop preproc time    : 0.000
% 0.60/0.77  #    Success case prop encoding time   : 0.000
% 0.60/0.77  #    Success case prop solver time     : 0.000
% 0.60/0.77  # Current number of processed clauses  : 800
% 0.60/0.77  #    Positive orientable unit clauses  : 64
% 0.60/0.77  #    Positive unorientable unit clauses: 0
% 0.60/0.77  #    Negative unit clauses             : 13
% 0.60/0.77  #    Non-unit-clauses                  : 723
% 0.60/0.77  # Current number of unprocessed clauses: 16691
% 0.60/0.77  # ...number of literals in the above   : 63421
% 0.60/0.77  # Current number of archived formulas  : 0
% 0.60/0.77  # Current number of archived clauses   : 74
% 0.60/0.77  # Clause-clause subsumption calls (NU) : 178234
% 0.60/0.77  # Rec. Clause-clause subsumption calls : 57419
% 0.60/0.77  # Non-unit clause-clause subsumptions  : 1050
% 0.60/0.77  # Unit Clause-clause subsumption calls : 8016
% 0.60/0.77  # Rewrite failures with RHS unbound    : 0
% 0.60/0.77  # BW rewrite match attempts            : 68
% 0.60/0.77  # BW rewrite match successes           : 5
% 0.60/0.77  # Condensation attempts                : 0
% 0.60/0.77  # Condensation successes               : 0
% 0.60/0.77  # Termbank termtop insertions          : 387111
% 0.60/0.77  
% 0.60/0.77  # -------------------------------------------------
% 0.60/0.77  # User time                : 0.410 s
% 0.60/0.77  # System time              : 0.021 s
% 0.60/0.77  # Total time               : 0.431 s
% 0.60/0.77  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
