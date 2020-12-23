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
% DateTime   : Thu Dec  3 11:19:33 EST 2020

% Result     : Theorem 55.19s
% Output     : CNFRefutation 55.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 382 expanded)
%              Number of clauses        :   55 ( 153 expanded)
%              Number of leaves         :   14 (  96 expanded)
%              Depth                    :   20
%              Number of atoms          :  378 (1778 expanded)
%              Number of equality atoms :   49 ( 218 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v7_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).

fof(d1_tex_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ( v7_struct_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & u1_struct_0(X1) = k6_domain_1(u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t5_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( u1_struct_0(X2) = u1_struct_0(X3)
               => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(d4_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_tex_2(X1,X2)
              <=> u1_struct_0(X3) = k6_domain_1(u1_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v7_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tex_2])).

fof(c_0_15,plain,(
    ! [X41,X43] :
      ( ( m1_subset_1(esk5_1(X41),u1_struct_0(X41))
        | ~ v7_struct_0(X41)
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41) )
      & ( u1_struct_0(X41) = k6_domain_1(u1_struct_0(X41),esk5_1(X41))
        | ~ v7_struct_0(X41)
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41) )
      & ( ~ m1_subset_1(X43,u1_struct_0(X41))
        | u1_struct_0(X41) != k6_domain_1(u1_struct_0(X41),X43)
        | v7_struct_0(X41)
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_1])])])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X51] :
      ( ~ v2_struct_0(esk6_0)
      & l1_pre_topc(esk6_0)
      & ~ v2_struct_0(esk7_0)
      & v7_struct_0(esk7_0)
      & m1_pre_topc(esk7_0,esk6_0)
      & ( ~ m1_subset_1(X51,u1_struct_0(esk6_0))
        | g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) != g1_pre_topc(u1_struct_0(k1_tex_2(esk6_0,X51)),u1_pre_topc(k1_tex_2(esk6_0,X51))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | l1_pre_topc(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_18,plain,(
    ! [X30] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | ~ v1_xboole_0(u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X14,X13)
        | r2_hidden(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ r2_hidden(X14,X13)
        | m1_subset_1(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ m1_subset_1(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_xboole_0(X13) )
      & ( ~ v1_xboole_0(X14)
        | m1_subset_1(X14,X13)
        | ~ v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk5_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v7_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | l1_struct_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_1(esk7_0),u1_struct_0(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

fof(c_0_34,plain,(
    ! [X17] :
      ( ~ l1_struct_0(X17)
      | k2_struct_0(X17) = u1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_35,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),u1_struct_0(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22])).

cnf(c_0_37,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_31])])).

cnf(c_0_40,plain,
    ( X1 = u1_struct_0(X2)
    | ~ l1_struct_0(X2)
    | ~ r1_tarski(k2_struct_0(X2),X1)
    | ~ r1_tarski(X1,k2_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),X1)
    | ~ l1_struct_0(esk7_0)
    | ~ r1_tarski(k2_struct_0(esk7_0),X1)
    | ~ r1_tarski(X1,k2_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),X1)
    | ~ r1_tarski(k2_struct_0(esk7_0),X1)
    | ~ r1_tarski(X1,k2_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_31])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

fof(c_0_46,plain,(
    ! [X18,X19,X20,X22,X24] :
      ( ( r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk2_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk2_3(X18,X19,X20),u1_pre_topc(X18))
        | ~ r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( X20 = k9_subset_1(u1_struct_0(X19),esk2_3(X18,X19,X20),k2_struct_0(X19))
        | ~ r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(X22,u1_pre_topc(X18))
        | X20 != k9_subset_1(u1_struct_0(X19),X22,k2_struct_0(X19))
        | r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk3_2(X18,X19),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( ~ r2_hidden(esk3_2(X18,X19),u1_pre_topc(X19))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(X24,u1_pre_topc(X18))
        | esk3_2(X18,X19) != k9_subset_1(u1_struct_0(X19),X24,k2_struct_0(X19))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk4_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | r2_hidden(esk3_2(X18,X19),u1_pre_topc(X19))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk4_2(X18,X19),u1_pre_topc(X18))
        | r2_hidden(esk3_2(X18,X19),u1_pre_topc(X19))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( esk3_2(X18,X19) = k9_subset_1(u1_struct_0(X19),esk4_2(X18,X19),k2_struct_0(X19))
        | r2_hidden(esk3_2(X18,X19),u1_pre_topc(X19))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),k2_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_45])])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_50,plain,(
    ! [X38,X39,X40] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_pre_topc(X39,X38)
      | ~ m1_pre_topc(X40,X38)
      | u1_struct_0(X39) != u1_struct_0(X40)
      | g1_pre_topc(u1_struct_0(X39),u1_pre_topc(X39)) = g1_pre_topc(u1_struct_0(X40),u1_pre_topc(X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_tsep_1])])])).

fof(c_0_51,plain,(
    ! [X47,X48] :
      ( ( ~ v2_struct_0(k1_tex_2(X47,X48))
        | v2_struct_0(X47)
        | ~ l1_pre_topc(X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47)) )
      & ( v1_pre_topc(k1_tex_2(X47,X48))
        | v2_struct_0(X47)
        | ~ l1_pre_topc(X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47)) )
      & ( m1_pre_topc(k1_tex_2(X47,X48),X47)
        | v2_struct_0(X47)
        | ~ l1_pre_topc(X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),X1)
    | ~ r1_tarski(k2_struct_0(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_54,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X2) != u1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_56,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),k2_struct_0(X1))
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_59,plain,(
    ! [X44,X45,X46] :
      ( ( X46 != k1_tex_2(X44,X45)
        | u1_struct_0(X46) = k6_domain_1(u1_struct_0(X44),X45)
        | v2_struct_0(X46)
        | ~ v1_pre_topc(X46)
        | ~ m1_pre_topc(X46,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ l1_pre_topc(X44) )
      & ( u1_struct_0(X46) != k6_domain_1(u1_struct_0(X44),X45)
        | X46 = k1_tex_2(X44,X45)
        | v2_struct_0(X46)
        | ~ v1_pre_topc(X46)
        | ~ m1_pre_topc(X46,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) != g1_pre_topc(u1_struct_0(k1_tex_2(esk6_0,X1)),u1_pre_topc(k1_tex_2(esk6_0,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | u1_struct_0(X1) != u1_struct_0(esk7_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_25]),c_0_26])])).

cnf(c_0_62,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk6_0,X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_26])])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),u1_struct_0(X1))
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_37]),c_0_30])).

fof(c_0_65,plain,(
    ! [X35,X36] :
      ( v1_xboole_0(X35)
      | ~ m1_subset_1(X36,X35)
      | k6_domain_1(X35,X36) = k1_tarski(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_66,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X2),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | X1 != k1_tex_2(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( v1_pre_topc(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk6_0,X1)) != u1_struct_0(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk5_1(esk7_0),u1_struct_0(X1))
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_30])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X1),esk5_1(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_73,plain,
    ( k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_56]),c_0_67]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(k1_tex_2(X1,X2)) != u1_struct_0(esk7_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_tarski(X1,esk6_0)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_38])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk5_1(esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_70]),c_0_25]),c_0_26])])).

cnf(c_0_76,plain,
    ( k1_tarski(esk5_1(X1)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_20]),c_0_27])).

cnf(c_0_77,plain,
    ( u1_struct_0(k1_tex_2(X1,X2)) = k1_tarski(X2)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk6_0,esk5_1(esk7_0))) != u1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_45])])).

cnf(c_0_79,plain,
    ( u1_struct_0(k1_tex_2(X1,esk5_1(X2))) = u1_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(esk5_1(X2),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_21]),c_0_26]),c_0_75])]),c_0_55]),c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_30]),c_0_31])])).

cnf(c_0_82,negated_conjecture,
    ( ~ l1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_81]),c_0_55])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_30]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:44:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 55.19/55.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 55.19/55.39  # and selection function PSelectUnlessUniqMaxPos.
% 55.19/55.39  #
% 55.19/55.39  # Preprocessing time       : 0.018 s
% 55.19/55.39  # Presaturation interreduction done
% 55.19/55.39  
% 55.19/55.39  # Proof found!
% 55.19/55.39  # SZS status Theorem
% 55.19/55.39  # SZS output start CNFRefutation
% 55.19/55.39  fof(t23_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v7_struct_0(X2))&m1_pre_topc(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tex_2)).
% 55.19/55.39  fof(d1_tex_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>(v7_struct_0(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&u1_struct_0(X1)=k6_domain_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_1)).
% 55.19/55.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 55.19/55.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 55.19/55.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 55.19/55.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 55.19/55.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 55.19/55.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 55.19/55.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 55.19/55.39  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 55.19/55.39  fof(t5_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(u1_struct_0(X2)=u1_struct_0(X3)=>g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tsep_1)).
% 55.19/55.39  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 55.19/55.39  fof(d4_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>(X3=k1_tex_2(X1,X2)<=>u1_struct_0(X3)=k6_domain_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 55.19/55.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 55.19/55.39  fof(c_0_14, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v7_struct_0(X2))&m1_pre_topc(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))))))), inference(assume_negation,[status(cth)],[t23_tex_2])).
% 55.19/55.39  fof(c_0_15, plain, ![X41, X43]:(((m1_subset_1(esk5_1(X41),u1_struct_0(X41))|~v7_struct_0(X41)|(v2_struct_0(X41)|~l1_struct_0(X41)))&(u1_struct_0(X41)=k6_domain_1(u1_struct_0(X41),esk5_1(X41))|~v7_struct_0(X41)|(v2_struct_0(X41)|~l1_struct_0(X41))))&(~m1_subset_1(X43,u1_struct_0(X41))|u1_struct_0(X41)!=k6_domain_1(u1_struct_0(X41),X43)|v7_struct_0(X41)|(v2_struct_0(X41)|~l1_struct_0(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_1])])])])])])).
% 55.19/55.39  fof(c_0_16, negated_conjecture, ![X51]:((~v2_struct_0(esk6_0)&l1_pre_topc(esk6_0))&(((~v2_struct_0(esk7_0)&v7_struct_0(esk7_0))&m1_pre_topc(esk7_0,esk6_0))&(~m1_subset_1(X51,u1_struct_0(esk6_0))|g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))!=g1_pre_topc(u1_struct_0(k1_tex_2(esk6_0,X51)),u1_pre_topc(k1_tex_2(esk6_0,X51)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 55.19/55.39  fof(c_0_17, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_pre_topc(X28,X27)|l1_pre_topc(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 55.19/55.39  fof(c_0_18, plain, ![X30]:(v2_struct_0(X30)|~l1_struct_0(X30)|~v1_xboole_0(u1_struct_0(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 55.19/55.39  fof(c_0_19, plain, ![X13, X14]:(((~m1_subset_1(X14,X13)|r2_hidden(X14,X13)|v1_xboole_0(X13))&(~r2_hidden(X14,X13)|m1_subset_1(X14,X13)|v1_xboole_0(X13)))&((~m1_subset_1(X14,X13)|v1_xboole_0(X14)|~v1_xboole_0(X13))&(~v1_xboole_0(X14)|m1_subset_1(X14,X13)|~v1_xboole_0(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 55.19/55.39  cnf(c_0_20, plain, (m1_subset_1(esk5_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 55.19/55.39  cnf(c_0_21, negated_conjecture, (v7_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 55.19/55.39  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 55.19/55.39  fof(c_0_23, plain, ![X26]:(~l1_pre_topc(X26)|l1_struct_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 55.19/55.39  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 55.19/55.39  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 55.19/55.39  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 55.19/55.39  cnf(c_0_27, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 55.19/55.39  cnf(c_0_28, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 55.19/55.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_1(esk7_0),u1_struct_0(esk7_0))|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 55.19/55.39  cnf(c_0_30, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 55.19/55.39  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 55.19/55.39  cnf(c_0_32, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 55.19/55.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_1(esk7_0),u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 55.19/55.39  fof(c_0_34, plain, ![X17]:(~l1_struct_0(X17)|k2_struct_0(X17)=u1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 55.19/55.39  fof(c_0_35, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 55.19/55.39  cnf(c_0_36, negated_conjecture, (r2_hidden(esk5_1(esk7_0),u1_struct_0(esk7_0))|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22])).
% 55.19/55.39  cnf(c_0_37, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 55.19/55.39  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 55.19/55.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk5_1(esk7_0),u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_30]), c_0_31])])).
% 55.19/55.39  cnf(c_0_40, plain, (X1=u1_struct_0(X2)|~l1_struct_0(X2)|~r1_tarski(k2_struct_0(X2),X1)|~r1_tarski(X1,k2_struct_0(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 55.19/55.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk5_1(esk7_0),X1)|~l1_struct_0(esk7_0)|~r1_tarski(k2_struct_0(esk7_0),X1)|~r1_tarski(X1,k2_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 55.19/55.39  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 55.19/55.39  fof(c_0_43, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 55.19/55.39  cnf(c_0_44, negated_conjecture, (r2_hidden(esk5_1(esk7_0),X1)|~r1_tarski(k2_struct_0(esk7_0),X1)|~r1_tarski(X1,k2_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30]), c_0_31])])).
% 55.19/55.39  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 55.19/55.39  fof(c_0_46, plain, ![X18, X19, X20, X22, X24]:(((r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&((((m1_subset_1(esk2_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))|~r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&(r2_hidden(esk2_3(X18,X19,X20),u1_pre_topc(X18))|~r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18)))&(X20=k9_subset_1(u1_struct_0(X19),esk2_3(X18,X19,X20),k2_struct_0(X19))|~r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18)))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X18)))|~r2_hidden(X22,u1_pre_topc(X18))|X20!=k9_subset_1(u1_struct_0(X19),X22,k2_struct_0(X19))|r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))))&((m1_subset_1(esk3_2(X18,X19),k1_zfmisc_1(u1_struct_0(X19)))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&((~r2_hidden(esk3_2(X18,X19),u1_pre_topc(X19))|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X18)))|~r2_hidden(X24,u1_pre_topc(X18))|esk3_2(X18,X19)!=k9_subset_1(u1_struct_0(X19),X24,k2_struct_0(X19)))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&(((m1_subset_1(esk4_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|r2_hidden(esk3_2(X18,X19),u1_pre_topc(X19))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&(r2_hidden(esk4_2(X18,X19),u1_pre_topc(X18))|r2_hidden(esk3_2(X18,X19),u1_pre_topc(X19))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18)))&(esk3_2(X18,X19)=k9_subset_1(u1_struct_0(X19),esk4_2(X18,X19),k2_struct_0(X19))|r2_hidden(esk3_2(X18,X19),u1_pre_topc(X19))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 55.19/55.39  cnf(c_0_47, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 55.19/55.39  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_1(esk7_0),k2_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_45])])).
% 55.19/55.39  cnf(c_0_49, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 55.19/55.39  fof(c_0_50, plain, ![X38, X39, X40]:(~l1_pre_topc(X38)|(~m1_pre_topc(X39,X38)|(~m1_pre_topc(X40,X38)|(u1_struct_0(X39)!=u1_struct_0(X40)|g1_pre_topc(u1_struct_0(X39),u1_pre_topc(X39))=g1_pre_topc(u1_struct_0(X40),u1_pre_topc(X40)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_tsep_1])])])).
% 55.19/55.39  fof(c_0_51, plain, ![X47, X48]:(((~v2_struct_0(k1_tex_2(X47,X48))|(v2_struct_0(X47)|~l1_pre_topc(X47)|~m1_subset_1(X48,u1_struct_0(X47))))&(v1_pre_topc(k1_tex_2(X47,X48))|(v2_struct_0(X47)|~l1_pre_topc(X47)|~m1_subset_1(X48,u1_struct_0(X47)))))&(m1_pre_topc(k1_tex_2(X47,X48),X47)|(v2_struct_0(X47)|~l1_pre_topc(X47)|~m1_subset_1(X48,u1_struct_0(X47))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 55.19/55.39  cnf(c_0_52, negated_conjecture, (r2_hidden(esk5_1(esk7_0),X1)|~r1_tarski(k2_struct_0(esk7_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 55.19/55.39  cnf(c_0_53, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_49, c_0_24])).
% 55.19/55.39  cnf(c_0_54, plain, (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|u1_struct_0(X2)!=u1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 55.19/55.39  cnf(c_0_55, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 55.19/55.39  cnf(c_0_56, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 55.19/55.39  cnf(c_0_57, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 55.19/55.39  cnf(c_0_58, negated_conjecture, (r2_hidden(esk5_1(esk7_0),k2_struct_0(X1))|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 55.19/55.39  fof(c_0_59, plain, ![X44, X45, X46]:((X46!=k1_tex_2(X44,X45)|u1_struct_0(X46)=k6_domain_1(u1_struct_0(X44),X45)|(v2_struct_0(X46)|~v1_pre_topc(X46)|~m1_pre_topc(X46,X44))|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~l1_pre_topc(X44)))&(u1_struct_0(X46)!=k6_domain_1(u1_struct_0(X44),X45)|X46=k1_tex_2(X44,X45)|(v2_struct_0(X46)|~v1_pre_topc(X46)|~m1_pre_topc(X46,X44))|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~l1_pre_topc(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).
% 55.19/55.39  cnf(c_0_60, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk6_0))|g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))!=g1_pre_topc(u1_struct_0(k1_tex_2(esk6_0,X1)),u1_pre_topc(k1_tex_2(esk6_0,X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 55.19/55.39  cnf(c_0_61, negated_conjecture, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))|u1_struct_0(X1)!=u1_struct_0(esk7_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_25]), c_0_26])])).
% 55.19/55.39  cnf(c_0_62, negated_conjecture, (m1_pre_topc(k1_tex_2(esk6_0,X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_26])])).
% 55.19/55.39  cnf(c_0_63, plain, (v2_struct_0(X1)|m1_subset_1(X2,u1_struct_0(X1))|~l1_struct_0(X1)|~r2_hidden(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_27, c_0_57])).
% 55.19/55.39  cnf(c_0_64, negated_conjecture, (r2_hidden(esk5_1(esk7_0),u1_struct_0(X1))|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_37]), c_0_30])).
% 55.19/55.39  fof(c_0_65, plain, ![X35, X36]:(v1_xboole_0(X35)|~m1_subset_1(X36,X35)|k6_domain_1(X35,X36)=k1_tarski(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 55.19/55.39  cnf(c_0_66, plain, (u1_struct_0(X1)=k6_domain_1(u1_struct_0(X2),X3)|v2_struct_0(X1)|v2_struct_0(X2)|X1!=k1_tex_2(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 55.19/55.39  cnf(c_0_67, plain, (v1_pre_topc(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 55.19/55.39  cnf(c_0_68, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 55.19/55.39  cnf(c_0_69, negated_conjecture, (u1_struct_0(k1_tex_2(esk6_0,X1))!=u1_struct_0(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 55.19/55.39  cnf(c_0_70, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(esk5_1(esk7_0),u1_struct_0(X1))|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_30])).
% 55.19/55.39  cnf(c_0_71, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 55.19/55.39  cnf(c_0_72, plain, (u1_struct_0(X1)=k6_domain_1(u1_struct_0(X1),esk5_1(X1))|v2_struct_0(X1)|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 55.19/55.39  cnf(c_0_73, plain, (k6_domain_1(u1_struct_0(X1),X2)=u1_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]), c_0_56]), c_0_67]), c_0_68])).
% 55.19/55.39  cnf(c_0_74, negated_conjecture, (u1_struct_0(k1_tex_2(X1,X2))!=u1_struct_0(esk7_0)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_tarski(X1,esk6_0)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_38])).
% 55.19/55.39  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk5_1(esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_70]), c_0_25]), c_0_26])])).
% 55.19/55.39  cnf(c_0_76, plain, (k1_tarski(esk5_1(X1))=u1_struct_0(X1)|v2_struct_0(X1)|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_20]), c_0_27])).
% 55.19/55.39  cnf(c_0_77, plain, (u1_struct_0(k1_tex_2(X1,X2))=k1_tarski(X2)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_71, c_0_73])).
% 55.19/55.39  cnf(c_0_78, negated_conjecture, (u1_struct_0(k1_tex_2(esk6_0,esk5_1(esk7_0)))!=u1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_45])])).
% 55.19/55.39  cnf(c_0_79, plain, (u1_struct_0(k1_tex_2(X1,esk5_1(X2)))=u1_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X2)|v1_xboole_0(u1_struct_0(X1))|~v7_struct_0(X2)|~l1_pre_topc(X1)|~l1_struct_0(X2)|~m1_subset_1(esk5_1(X2),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 55.19/55.39  cnf(c_0_80, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_21]), c_0_26]), c_0_75])]), c_0_55]), c_0_22])).
% 55.19/55.39  cnf(c_0_81, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_30]), c_0_31])])).
% 55.19/55.39  cnf(c_0_82, negated_conjecture, (~l1_struct_0(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_81]), c_0_55])).
% 55.19/55.39  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_30]), c_0_26])]), ['proof']).
% 55.19/55.39  # SZS output end CNFRefutation
% 55.19/55.39  # Proof object total steps             : 84
% 55.19/55.39  # Proof object clause steps            : 55
% 55.19/55.39  # Proof object formula steps           : 29
% 55.19/55.39  # Proof object conjectures             : 31
% 55.19/55.39  # Proof object clause conjectures      : 28
% 55.19/55.39  # Proof object formula conjectures     : 3
% 55.19/55.39  # Proof object initial clauses used    : 24
% 55.19/55.39  # Proof object initial formulas used   : 14
% 55.19/55.39  # Proof object generating inferences   : 28
% 55.19/55.39  # Proof object simplifying inferences  : 43
% 55.19/55.39  # Training examples: 0 positive, 0 negative
% 55.19/55.39  # Parsed axioms                        : 19
% 55.19/55.39  # Removed by relevancy pruning/SinE    : 0
% 55.19/55.39  # Initial clauses                      : 46
% 55.19/55.39  # Removed in clause preprocessing      : 0
% 55.19/55.39  # Initial clauses in saturation        : 46
% 55.19/55.39  # Processed clauses                    : 180790
% 55.19/55.39  # ...of these trivial                  : 709
% 55.19/55.39  # ...subsumed                          : 159618
% 55.19/55.39  # ...remaining for further processing  : 20463
% 55.19/55.39  # Other redundant clauses eliminated   : 21435
% 55.19/55.39  # Clauses deleted for lack of memory   : 264175
% 55.19/55.39  # Backward-subsumed                    : 4594
% 55.19/55.39  # Backward-rewritten                   : 1001
% 55.19/55.39  # Generated clauses                    : 3089005
% 55.19/55.39  # ...of the previous two non-trivial   : 3003608
% 55.19/55.39  # Contextual simplify-reflections      : 1202
% 55.19/55.39  # Paramodulations                      : 3067227
% 55.19/55.39  # Factorizations                       : 310
% 55.19/55.39  # Equation resolutions                 : 21450
% 55.19/55.39  # Propositional unsat checks           : 0
% 55.19/55.39  #    Propositional check models        : 0
% 55.19/55.39  #    Propositional check unsatisfiable : 0
% 55.19/55.39  #    Propositional clauses             : 0
% 55.19/55.39  #    Propositional clauses after purity: 0
% 55.19/55.39  #    Propositional unsat core size     : 0
% 55.19/55.39  #    Propositional preprocessing time  : 0.000
% 55.19/55.39  #    Propositional encoding time       : 0.000
% 55.19/55.39  #    Propositional solver time         : 0.000
% 55.19/55.39  #    Success case prop preproc time    : 0.000
% 55.19/55.39  #    Success case prop encoding time   : 0.000
% 55.19/55.39  #    Success case prop solver time     : 0.000
% 55.19/55.39  # Current number of processed clauses  : 14803
% 55.19/55.39  #    Positive orientable unit clauses  : 478
% 55.19/55.39  #    Positive unorientable unit clauses: 0
% 55.19/55.39  #    Negative unit clauses             : 191
% 55.19/55.39  #    Non-unit-clauses                  : 14134
% 55.19/55.39  # Current number of unprocessed clauses: 1021015
% 55.19/55.39  # ...number of literals in the above   : 7659211
% 55.19/55.39  # Current number of archived formulas  : 0
% 55.19/55.39  # Current number of archived clauses   : 5656
% 55.19/55.39  # Clause-clause subsumption calls (NU) : 25623232
% 55.19/55.39  # Rec. Clause-clause subsumption calls : 1326168
% 55.19/55.39  # Non-unit clause-clause subsumptions  : 116765
% 55.19/55.39  # Unit Clause-clause subsumption calls : 281956
% 55.19/55.39  # Rewrite failures with RHS unbound    : 0
% 55.19/55.39  # BW rewrite match attempts            : 4403
% 55.19/55.39  # BW rewrite match successes           : 242
% 55.19/55.39  # Condensation attempts                : 0
% 55.19/55.39  # Condensation successes               : 0
% 55.19/55.39  # Termbank termtop insertions          : 101452548
% 55.23/55.47  
% 55.23/55.47  # -------------------------------------------------
% 55.23/55.47  # User time                : 54.132 s
% 55.23/55.47  # System time              : 0.980 s
% 55.23/55.47  # Total time               : 55.113 s
% 55.23/55.47  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
