%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t47_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:40 EDT 2019

% Result     : Theorem 239.59s
% Output     : CNFRefutation 239.59s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 563 expanded)
%              Number of clauses        :   54 ( 215 expanded)
%              Number of leaves         :   14 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  376 (2357 expanded)
%              Number of equality atoms :   48 ( 141 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   70 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( v1_tops_2(X3,X1)
               => v1_tops_2(k1_tops_2(X1,X2,X3),k1_pre_topc(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',t47_tops_2)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',dt_k1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',dt_l1_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',d10_pre_topc)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',dt_k2_struct_0)).

fof(dt_k1_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',dt_k1_tops_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',redefinition_k9_subset_1)).

fof(d3_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
                 => ( X4 = k1_tops_2(X1,X2,X3)
                  <=> ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
                       => ( r2_hidden(X5,X4)
                        <=> ? [X6] :
                              ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
                              & r2_hidden(X6,X3)
                              & k9_subset_1(u1_struct_0(X1),X6,X2) = X5 ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',d3_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',t4_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',dt_k9_subset_1)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',d1_tops_2)).

fof(t32_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v3_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',t32_tops_2)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t47_tops_2.p',commutativity_k9_subset_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( v1_tops_2(X3,X1)
                 => v1_tops_2(k1_tops_2(X1,X2,X3),k1_pre_topc(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_tops_2])).

fof(c_0_15,plain,(
    ! [X37,X38] :
      ( ( v1_pre_topc(k1_pre_topc(X37,X38))
        | ~ l1_pre_topc(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))) )
      & ( m1_pre_topc(k1_pre_topc(X37,X38),X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & v1_tops_2(esk3_0,esk1_0)
    & ~ v1_tops_2(k1_tops_2(esk1_0,esk2_0,esk3_0),k1_pre_topc(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X47,X48] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_pre_topc(X48,X47)
      | l1_pre_topc(X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_18,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X46] :
      ( ~ l1_pre_topc(X46)
      | l1_struct_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_22,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ( X20 != k1_pre_topc(X18,X19)
        | k2_struct_0(X20) = X19
        | ~ v1_pre_topc(X20)
        | ~ m1_pre_topc(X20,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( k2_struct_0(X20) != X19
        | X20 = k1_pre_topc(X18,X19)
        | ~ v1_pre_topc(X20)
        | ~ m1_pre_topc(X20,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_25,plain,(
    ! [X42] :
      ( ~ l1_struct_0(X42)
      | m1_subset_1(k2_struct_0(X42),k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_26,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_20])])).

cnf(c_0_28,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_30,plain,(
    ! [X39,X40,X41] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | ~ m1_subset_1(X41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X39))))
      | m1_subset_1(k1_tops_2(X39,X40,X41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X39,X40))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( l1_struct_0(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29]),c_0_18])).

fof(c_0_34,plain,(
    ! [X64,X65,X66] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(X64))
      | k9_subset_1(X64,X65,X66) = k3_xboole_0(X65,X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_35,plain,(
    ! [X25,X26,X27,X28,X29,X31,X33] :
      ( ( m1_subset_1(esk5_5(X25,X26,X27,X28,X29),k1_zfmisc_1(u1_struct_0(X25)))
        | ~ r2_hidden(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26))))
        | X28 != k1_tops_2(X25,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26)))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( r2_hidden(esk5_5(X25,X26,X27,X28,X29),X27)
        | ~ r2_hidden(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26))))
        | X28 != k1_tops_2(X25,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26)))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( k9_subset_1(u1_struct_0(X25),esk5_5(X25,X26,X27,X28,X29),X26) = X29
        | ~ r2_hidden(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26))))
        | X28 != k1_tops_2(X25,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26)))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ r2_hidden(X31,X27)
        | k9_subset_1(u1_struct_0(X25),X31,X26) != X29
        | r2_hidden(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26))))
        | X28 != k1_tops_2(X25,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26)))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk6_4(X25,X26,X27,X28),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26))))
        | X28 = k1_tops_2(X25,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26)))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( ~ r2_hidden(esk6_4(X25,X26,X27,X28),X28)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ r2_hidden(X33,X27)
        | k9_subset_1(u1_struct_0(X25),X33,X26) != esk6_4(X25,X26,X27,X28)
        | X28 = k1_tops_2(X25,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26)))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk7_4(X25,X26,X27,X28),k1_zfmisc_1(u1_struct_0(X25)))
        | r2_hidden(esk6_4(X25,X26,X27,X28),X28)
        | X28 = k1_tops_2(X25,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26)))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( r2_hidden(esk7_4(X25,X26,X27,X28),X27)
        | r2_hidden(esk6_4(X25,X26,X27,X28),X28)
        | X28 = k1_tops_2(X25,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26)))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( k9_subset_1(u1_struct_0(X25),esk7_4(X25,X26,X27,X28),X26) = esk6_4(X25,X26,X27,X28)
        | r2_hidden(esk6_4(X25,X26,X27,X28),X28)
        | X28 = k1_tops_2(X25,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26)))))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).

fof(c_0_36,plain,(
    ! [X79,X80,X81] :
      ( ~ r2_hidden(X79,X80)
      | ~ m1_subset_1(X80,k1_zfmisc_1(X81))
      | m1_subset_1(X79,X81) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_39,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X43))
      | m1_subset_1(k9_subset_1(X43,X44,X45),k1_zfmisc_1(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k2_struct_0(k1_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk1_0,esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_19]),c_0_20])])).

cnf(c_0_42,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v1_tops_2(X22,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X23,X22)
        | v3_pre_topc(X23,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk4_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))
        | v1_tops_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk4_2(X21,X22),X22)
        | v1_tops_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) )
      & ( ~ v3_pre_topc(esk4_2(X21,X22),X21)
        | v1_tops_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk5_5(X1,X2,X3,X4,X5),X3)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k1_tops_2(esk1_0,X1,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_20])])).

fof(c_0_47,plain,(
    ! [X72,X73,X74,X76] :
      ( ( m1_subset_1(esk12_3(X72,X73,X74),k1_zfmisc_1(u1_struct_0(X72)))
        | ~ v3_pre_topc(X74,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X73)))
        | ~ m1_pre_topc(X73,X72)
        | ~ l1_pre_topc(X72) )
      & ( v3_pre_topc(esk12_3(X72,X73,X74),X72)
        | ~ v3_pre_topc(X74,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X73)))
        | ~ m1_pre_topc(X73,X72)
        | ~ l1_pre_topc(X72) )
      & ( k9_subset_1(u1_struct_0(X73),esk12_3(X72,X73,X74),k2_struct_0(X73)) = X74
        | ~ v3_pre_topc(X74,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X73)))
        | ~ m1_pre_topc(X73,X72)
        | ~ l1_pre_topc(X72) )
      & ( ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X72)))
        | ~ v3_pre_topc(X76,X72)
        | k9_subset_1(u1_struct_0(X73),X76,k2_struct_0(X73)) != X74
        | v3_pre_topc(X74,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X73)))
        | ~ m1_pre_topc(X73,X72)
        | ~ l1_pre_topc(X72) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_tops_2])])])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_19])).

cnf(c_0_51,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( r2_hidden(esk5_5(X1,X2,X3,X4,X5),X3)
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k1_tops_2(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_tops_2(k1_tops_2(esk1_0,esk2_0,esk3_0),k1_pre_topc(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_56,plain,
    ( k9_subset_1(u1_struct_0(X1),esk5_5(X1,X2,X3,X4,X5),X2) = X5
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_57,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X15))
      | k9_subset_1(X15,X16,X17) = k9_subset_1(X15,X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_58,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_59,plain,
    ( v3_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),X1,esk2_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( k9_subset_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),X1,esk2_0) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_49]),c_0_50])).

cnf(c_0_62,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_51,c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( v1_tops_2(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_64,plain,
    ( r2_hidden(esk5_5(X1,X2,X3,k1_tops_2(X1,X2,X3),X4),X3)
    | ~ r2_hidden(X4,k1_tops_2(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_37])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk4_2(k1_pre_topc(esk1_0,esk2_0),k1_tops_2(esk1_0,esk2_0,esk3_0)),k1_tops_2(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_27])]),c_0_55])).

cnf(c_0_66,plain,
    ( k9_subset_1(u1_struct_0(X1),esk5_5(X1,X2,X3,X4,X5),X2) = X5
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_56,c_0_45])).

cnf(c_0_67,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(X1)))
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_58,c_0_45])).

cnf(c_0_69,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_38]),c_0_20])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk5_5(esk1_0,esk2_0,esk3_0,k1_tops_2(esk1_0,esk2_0,esk3_0),esk4_2(k1_pre_topc(esk1_0,esk2_0),k1_tops_2(esk1_0,esk2_0,esk3_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_38]),c_0_19]),c_0_20])])).

cnf(c_0_73,plain,
    ( k9_subset_1(u1_struct_0(X1),esk5_5(X1,X2,X3,k1_tops_2(X1,X2,X3),X4),X2) = X4
    | ~ r2_hidden(X4,k1_tops_2(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_37])).

cnf(c_0_74,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_19])).

cnf(c_0_75,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,k1_tops_2(X1,X2,X3),X4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,k1_tops_2(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_37])).

cnf(c_0_76,negated_conjecture,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0),k1_pre_topc(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_41]),c_0_61]),c_0_61]),c_0_70])])).

cnf(c_0_77,negated_conjecture,
    ( v3_pre_topc(esk5_5(esk1_0,esk2_0,esk3_0,k1_tops_2(esk1_0,esk2_0,esk3_0),esk4_2(k1_pre_topc(esk1_0,esk2_0),k1_tops_2(esk1_0,esk2_0,esk3_0))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk5_5(esk1_0,esk2_0,esk3_0,k1_tops_2(esk1_0,esk2_0,esk3_0),esk4_2(k1_pre_topc(esk1_0,esk2_0),k1_tops_2(esk1_0,esk2_0,esk3_0)))) = esk4_2(k1_pre_topc(esk1_0,esk2_0),k1_tops_2(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_65]),c_0_38]),c_0_19]),c_0_20])]),c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk5_5(esk1_0,esk2_0,esk3_0,k1_tops_2(esk1_0,esk2_0,esk3_0),esk4_2(k1_pre_topc(esk1_0,esk2_0),k1_tops_2(esk1_0,esk2_0,esk3_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_65]),c_0_38]),c_0_19]),c_0_20])])).

cnf(c_0_80,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk4_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_81,negated_conjecture,
    ( v3_pre_topc(esk4_2(k1_pre_topc(esk1_0,esk2_0),k1_tops_2(esk1_0,esk2_0,esk3_0)),k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_74]),c_0_78]),c_0_23]),c_0_79]),c_0_20])])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_54]),c_0_27])]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
