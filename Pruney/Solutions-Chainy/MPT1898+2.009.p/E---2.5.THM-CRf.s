%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:55 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 447 expanded)
%              Number of clauses        :   34 ( 176 expanded)
%              Number of leaves         :    7 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          :  240 (2215 expanded)
%              Number of equality atoms :   12 (  74 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   54 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2) )
                     => ( X3 = X4
                        | r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X4))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tex_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t66_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t65_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ~ ( r1_tarski(X2,X3)
                      & v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ v2_tex_2(X14,X13)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X14)
        | X15 = X16
        | r1_xboole_0(k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),X15)),k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),X16)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk1_2(X13,X14),u1_struct_0(X13))
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_2(X13,X14),u1_struct_0(X13))
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( esk1_2(X13,X14) != esk2_2(X13,X14)
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r1_xboole_0(k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),esk1_2(X13,X14))),k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),esk2_2(X13,X14))))
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tex_2])])])])])])).

fof(c_0_8,plain,(
    ! [X7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ? [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            & v3_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t66_tex_2])).

fof(c_0_10,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,(
    ! [X23] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & v3_tdlat_3(esk4_0)
      & l1_pre_topc(esk4_0)
      & ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v3_tex_2(X23,esk4_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | v2_struct_0(X1)
    | r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v3_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | r2_hidden(esk1_2(esk4_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | m1_subset_1(esk1_2(esk4_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | r1_tarski(esk1_2(esk4_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( esk1_2(esk4_0,k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | m1_subset_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | v2_tex_2(k1_xboole_0,X1)
    | v2_struct_0(X1)
    | r2_hidden(esk2_2(X1,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | r2_hidden(esk2_2(esk4_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | m1_subset_1(esk2_2(esk4_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

fof(c_0_36,plain,(
    ! [X19,X20] :
      ( ( m1_subset_1(esk3_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ v3_tdlat_3(X19)
        | ~ l1_pre_topc(X19) )
      & ( r1_tarski(X20,esk3_2(X19,X20))
        | ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ v3_tdlat_3(X19)
        | ~ l1_pre_topc(X19) )
      & ( v3_tex_2(esk3_2(X19,X20),X19)
        | ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ v3_tdlat_3(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | r1_tarski(esk2_2(esk4_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_35])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,plain,
    ( v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | esk1_2(X1,X2) != esk2_2(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,negated_conjecture,
    ( esk2_2(esk4_0,k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_41,plain,
    ( v3_tex_2(esk3_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_17]),c_0_18]),c_0_19]),c_0_12])]),c_0_20]),c_0_30])).

cnf(c_0_44,plain,
    ( v3_tex_2(esk3_2(X1,k1_xboole_0),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_tex_2(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( v3_tex_2(esk3_2(esk4_0,k1_xboole_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:16:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.15/0.39  # and selection function SelectGrCQArEqFirst.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.029 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t59_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r2_hidden(X4,X2))=>(X3=X4|r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X4)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tex_2)).
% 0.15/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.15/0.39  fof(t66_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 0.15/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.15/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.15/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.15/0.39  fof(t65_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X2,X3)&v3_tex_2(X3,X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 0.15/0.39  fof(c_0_7, plain, ![X13, X14, X15, X16]:((~v2_tex_2(X14,X13)|(~m1_subset_1(X15,u1_struct_0(X13))|(~m1_subset_1(X16,u1_struct_0(X13))|(~r2_hidden(X15,X14)|~r2_hidden(X16,X14)|(X15=X16|r1_xboole_0(k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),X15)),k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),X16)))))))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&((m1_subset_1(esk1_2(X13,X14),u1_struct_0(X13))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&((m1_subset_1(esk2_2(X13,X14),u1_struct_0(X13))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&(((r2_hidden(esk1_2(X13,X14),X14)|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&(r2_hidden(esk2_2(X13,X14),X14)|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13))))&((esk1_2(X13,X14)!=esk2_2(X13,X14)|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&(~r1_xboole_0(k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),esk1_2(X13,X14))),k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),esk2_2(X13,X14))))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tex_2])])])])])])).
% 0.15/0.39  fof(c_0_8, plain, ![X7]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.15/0.39  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t66_tex_2])).
% 0.15/0.39  fof(c_0_10, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.15/0.39  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.39  cnf(c_0_12, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.39  fof(c_0_13, negated_conjecture, ![X23]:((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v3_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_tex_2(X23,esk4_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.15/0.39  fof(c_0_14, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.15/0.39  cnf(c_0_15, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.39  cnf(c_0_16, plain, (v2_tex_2(k1_xboole_0,X1)|v2_struct_0(X1)|r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)|~l1_pre_topc(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.15/0.39  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_18, negated_conjecture, (v3_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  fof(c_0_21, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.15/0.39  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_23, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_12])).
% 0.15/0.39  cnf(c_0_24, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|r2_hidden(esk1_2(esk4_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.15/0.39  cnf(c_0_25, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.39  cnf(c_0_26, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_12])).
% 0.15/0.39  cnf(c_0_27, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|m1_subset_1(esk1_2(esk4_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.15/0.39  cnf(c_0_28, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.39  cnf(c_0_29, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|r1_tarski(esk1_2(esk4_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_22, c_0_27])).
% 0.15/0.39  cnf(c_0_30, negated_conjecture, (esk1_2(esk4_0,k1_xboole_0)=k1_xboole_0|v2_tex_2(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.15/0.39  cnf(c_0_31, plain, (r2_hidden(esk2_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.39  cnf(c_0_32, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|m1_subset_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.15/0.39  cnf(c_0_33, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|v2_tex_2(k1_xboole_0,X1)|v2_struct_0(X1)|r2_hidden(esk2_2(X1,k1_xboole_0),k1_xboole_0)|~l1_pre_topc(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.15/0.39  cnf(c_0_34, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|r2_hidden(esk2_2(esk4_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.15/0.39  cnf(c_0_35, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|m1_subset_1(esk2_2(esk4_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 0.15/0.39  fof(c_0_36, plain, ![X19, X20]:((m1_subset_1(esk3_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))|~v2_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~v3_tdlat_3(X19)|~l1_pre_topc(X19)))&((r1_tarski(X20,esk3_2(X19,X20))|~v2_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~v3_tdlat_3(X19)|~l1_pre_topc(X19)))&(v3_tex_2(esk3_2(X19,X20),X19)|~v2_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~v3_tdlat_3(X19)|~l1_pre_topc(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).
% 0.15/0.39  cnf(c_0_37, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|r1_tarski(esk2_2(esk4_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_22, c_0_35])).
% 0.15/0.39  cnf(c_0_38, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.15/0.39  cnf(c_0_39, plain, (v2_tex_2(X2,X1)|v2_struct_0(X1)|esk1_2(X1,X2)!=esk2_2(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.39  cnf(c_0_40, negated_conjecture, (esk2_2(esk4_0,k1_xboole_0)=k1_xboole_0|v2_tex_2(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 0.15/0.39  cnf(c_0_41, plain, (v3_tex_2(esk3_2(X1,X2),X1)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.15/0.39  cnf(c_0_42, plain, (v2_struct_0(X1)|m1_subset_1(esk3_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_12])).
% 0.15/0.39  cnf(c_0_43, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_17]), c_0_18]), c_0_19]), c_0_12])]), c_0_20]), c_0_30])).
% 0.15/0.39  cnf(c_0_44, plain, (v3_tex_2(esk3_2(X1,k1_xboole_0),X1)|v2_struct_0(X1)|~v2_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_12])).
% 0.15/0.39  cnf(c_0_45, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_tex_2(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.15/0.39  cnf(c_0_47, negated_conjecture, (v3_tex_2(esk3_2(esk4_0,k1_xboole_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.15/0.39  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 49
% 0.15/0.39  # Proof object clause steps            : 34
% 0.15/0.39  # Proof object formula steps           : 15
% 0.15/0.39  # Proof object conjectures             : 22
% 0.15/0.39  # Proof object clause conjectures      : 19
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 14
% 0.15/0.39  # Proof object initial formulas used   : 7
% 0.15/0.39  # Proof object generating inferences   : 20
% 0.15/0.39  # Proof object simplifying inferences  : 27
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 7
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 22
% 0.15/0.39  # Removed in clause preprocessing      : 0
% 0.15/0.39  # Initial clauses in saturation        : 22
% 0.15/0.39  # Processed clauses                    : 91
% 0.15/0.39  # ...of these trivial                  : 0
% 0.15/0.39  # ...subsumed                          : 14
% 0.15/0.39  # ...remaining for further processing  : 77
% 0.15/0.39  # Other redundant clauses eliminated   : 2
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 3
% 0.15/0.39  # Backward-rewritten                   : 14
% 0.15/0.39  # Generated clauses                    : 113
% 0.15/0.39  # ...of the previous two non-trivial   : 95
% 0.15/0.39  # Contextual simplify-reflections      : 3
% 0.15/0.39  # Paramodulations                      : 111
% 0.15/0.39  # Factorizations                       : 0
% 0.15/0.39  # Equation resolutions                 : 2
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 37
% 0.15/0.39  #    Positive orientable unit clauses  : 10
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 3
% 0.15/0.39  #    Non-unit-clauses                  : 24
% 0.15/0.39  # Current number of unprocessed clauses: 9
% 0.15/0.39  # ...number of literals in the above   : 58
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 38
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 542
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 152
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 15
% 0.15/0.39  # Unit Clause-clause subsumption calls : 13
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 5
% 0.15/0.39  # BW rewrite match successes           : 2
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 4492
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.034 s
% 0.15/0.39  # System time              : 0.004 s
% 0.15/0.39  # Total time               : 0.038 s
% 0.15/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
